--- An immutable hashmap, modelled after PersistentHashMap in Clojure.
--  Hashmaps much like lua tables in that they map keys to values:
--
--  	local my_map = Hashmap.from { foo = 'bar', [2] = 'baz' }
--  	print(my_map:get('foo')) -- 'bar'
--
--  But because they are persistent, modifications create a new Hashmap instead
--  of changing the old one:
--
--  	local my_new_map = my_map:assoc('foo', 42)
--  	print(my_new_map:get('foo')) -- 42
--  	print(my_map:get('foo')) -- still 'bar'
--
--  It is internally implemented as a Hash Array Mapped Trie (HAMT), which you
--  can learn more about from the [Wikipedia article][1].
--
--  [1]: https://en.wikipedia.org/wiki/Hash_array_mapped_trie
--
--  @module Hashmap
--

-- Implementation Details:
-- =======================
-- For my own sanity, I used <http://git.io/vJeZx> as my model.
-- To match Lua's index-by-one semantics I had to introduce an offset or two.
-- Every line I've done that on is marked with a +1 or -1 comment.

-- Locals for performance and clarity
local type = type; local pairs = pairs; local ipairs = ipairs; local next = next; local select = select
local setmetatable = setmetatable; local getmetatable = getmetatable; local table_insert = table.insert
local table_remove = table.remove; local pcall = pcall; local assert = assert; local error = error

local function try(...)
    local ok, r = pcall(...); if not ok then return nil, r end; return r
end

-- Localized external dependencies
local fun = require 'ltrie.fun'
local b_mod = try(require, 'bit32') or try(require, 'bit'); if not b_mod then error("Hashmap: No bit library found.") end
local b_band = b_mod.band; local b_bor = b_mod.bor; local b_bnot = b_mod.bnot; local b_lshift = b_mod.lshift; local b_rshift =
    b_mod.rshift
local hashcode_func = require 'ltrie.hashcode'.hashcode

-- Forward declarations
local Node, Leaf, CLeaf, Node_mt, Leaf_mt, CLeaf_mt, NodeC, LeafC, CLeafC, merge_nodes

--- @class Hashmap The Hashmap class table containing static and instance methods.
--- @field count number Number of key-value pairs in the map
--- @field root table The root node of the trie (Node, Leaf, CLeaf, or EmptyRoot)
--- @field _mutate table|nil Optional mutation token (unique table reference)
local Hash = {};
local mt = { __index = Hash } -- Metatable for Hmap instances

-- Hmap instance constructor
--- @private
--- @param data {count: number, root: table, _mutate?: table}
--- @return Hashmap instance
local function Hmap(data)
    assert(type(data) == 'table' and data.count ~= nil and data.count >= 0 and data.root, "Invalid Hmap data"); return
        setmetatable(data, mt)
end
-- Public constructors
--- Creates a hashmap from an iterator or table.
-- @param ... Iterator function arguments OR a single table.
-- @return Hashmap A new immutable Hashmap instance.
function Hash.from(...)
    local r = Hash.EMPTY:asMutable(); fun.each(function(k, v) r = r:assoc(k, v) end, ...); r = r:asImmutable(); return r
end

--- Creates a hashmap from alternating key/value arguments.
-- @param ... Alternating keys and values (k1, v1, ...).
-- @return Hashmap A new immutable Hashmap instance.
function Hash.of(...)
    local r = Hash.EMPTY:asMutable(); local n = select('#', ...); for i = 1, n, 2 do
        local k = select(i, ...)
        if i + 1 <= n then r = r:assoc(k, select(i + 1, ...)) end
    end; r = r:asImmutable(); return r
end

-- {{{ Nodes Definition and Implementation
-- [MERGE RESTORED] Interface check includes merge again
local function implements_node(o)
    assert(o.assoc and o.without and o.find and o.iter and o.merge,
        "Node type missing method(s)")
end
local BITS = 5; local MASK = b_lshift(1, BITS) - 1

local function mask(h, s) return b_lshift(1, b_band(b_rshift(h, s), MASK)) end
-- popcount {{{
local pc_m1 = 0x55555555; local pc_m2 = 0x33333333; local pc_m4 = 0x0f0f0f0f
local function popCount(x)
    x = x or 0; x = x - b_band(b_rshift(x, 1), pc_m1); x = b_band(x, pc_m2) + b_band(b_rshift(x, 2), pc_m2); x = b_band(
        x + b_rshift(x, 4), pc_m4); x = x + b_rshift(x, 8); x = x + b_rshift(x, 16); return b_band(x, 0x3f)
end
-- }}}
local function idxFor(bm, b) return popCount(b_band(bm, b - 1)) + 1 end

-- Copy Functions {{{
local function copy_nodes_array(tbl)
    assert(type(tbl) == 'table', "Bad nodes"); local t = {}; local N = #tbl; for i = 1, N do t[i] = tbl[i] end; return t
end
local function copy_node_instance(owner, node_inst)
    assert(node_inst, "Cannot copy nil node");
    local t = {}; local mt_node = getmetatable(node_inst); assert(mt_node, "Node lacks mt");
    if mt_node == Node_mt then
        assert(node_inst.bitmap ~= nil and node_inst.nodes and node_inst.shift ~= nil, "copy: Original Node invalid!")
    elseif mt_node == Leaf_mt then
        assert(node_inst.hash ~= nil, "copy: Original Leaf invalid!")
    elseif mt_node == CLeaf_mt then
        assert(node_inst.hash ~= nil and node_inst.leaves, "copy: Original CLeaf invalid!")
    elseif mt_node.name ~= "EmptyRoot" then
        print("Warning: copy_node_instance copying unknown type: " .. (mt_node.name or "unknown"))
    end
    for k, v in pairs(node_inst) do if k ~= "_mutate" then t[k] = v end end
    if owner and owner._mutate then t._mutate = owner._mutate end;
    return setmetatable(t, mt_node)
end
-- }}}

-- Node Type {{{
--- @class Node Internal HAMT Node
--- @field bitmap number Bitmap indicating child presence.
--- @field nodes table[] Array of child nodes (Node, Leaf, CLeaf)
--- @field shift number The current shift level in the trie
--- @field _mutate table|nil Optional mutation token (table reference)
Node = {}; Node_mt = { name = "Node", __index = Node }
--- @private Node Constructor
function NodeC(data)
    assert(data.bitmap ~= nil and data.nodes and data.shift ~= nil, "Invalid Node data"); return setmetatable(data,
        Node_mt)
end

--- @private Node Factory - Used when assoc needs to split/create structure
function Node.create(shift, node1, hash2, key2, val2)
    assert(node1 and node1.hash, "Node.create: node1 invalid/missing hash")
    local h1 = node1.hash; local fr1 = b_band(b_rshift(h1, shift), MASK); local fr2 = b_band(b_rshift(hash2, shift), MASK)
    if fr1 == fr2 then                                                              -- Collision: must create deeper structure using merge logic
        local empty = NodeC { bitmap = 0, nodes = {}, shift = shift + BITS }
        local n1, d1 = merge_nodes(empty, shift + BITS, node1, nil)                 -- Merge first item into empty deeper node
        local n2, d2 = merge_nodes(n1, shift + BITS, LeafC(hash2, key2, val2), nil) -- Merge second item into result
        assert(n2 == nil or type(n2) == 'table', "Node.create: merge result n2 invalid type")
        if n2 == nil then return nil end                                            -- Should not happen if merging non-nil items
        return NodeC { bitmap = mask(h1, shift), nodes = { n2 }, shift = shift }
    else                                                                            -- Distinct fragments: create node containing both items directly
        local nl2 = LeafC(hash2, key2, val2); local bm = b_bor(mask(h1, shift), mask(hash2, shift)); local nodes = (fr1 < fr2) and
            { node1, nl2 } or { nl2, node1 }
        return NodeC { bitmap = bm, nodes = nodes, shift = shift }
    end
end

--- @private Node method
function Node:assoc(s, h, k, v)
    local o = self._mutate and self or nil; local b = mask(h, s); local i = idxFor(self.bitmap, b); if b_band(self.bitmap, b) ~= 0 then
        local ex = self.nodes[i]; assert(ex, "N:assoc inconsistent"); local nn, upd = ex:assoc(s + BITS, h, k, v); if nn == ex then
            return
                self, upd
        end; local na = copy_nodes_array(self.nodes); na[i] = nn; local r = copy_node_instance(o, self); r.nodes =
            na; return r, upd
    else
        local nl = LeafC(h, k, v); local na = copy_nodes_array(self.nodes); table_insert(na, i, nl); local r =
            copy_node_instance(o, self); r.bitmap = b_bor(self.bitmap, b); r.nodes = na; return r, false
    end
end

--- @private Node method
function Node:without(s, h, k)
    local o = self._mutate and self or nil; local b = mask(h, s); if b_band(self.bitmap, b) == 0 then return self end
    local i = idxFor(self.bitmap, b); local nR = self.nodes[i]; assert(nR, "N:without inconsistent")
    local nA = nR:without(s + BITS, h, k); if nA == nR then return self end
    if nA == nil then
        if #self.nodes == 1 then
            return nil
        end -- End added V9
        local na = copy_nodes_array(self.nodes); table_remove(na, i); local r = copy_node_instance(o, self); r.bitmap =
            b_band(self.bitmap, b_bnot(b)); r.nodes = na; return r
    else
        local na = copy_nodes_array(self.nodes); na[i] = nA; local r = copy_node_instance(o, self); r.nodes = na; return
            r
    end
end

--- @private Node method
function Node:find(s, h, k)
    local b = mask(h, s); if b_band(self.bitmap, b) ~= 0 then
        local i = idxFor(self.bitmap, b); local n = self.nodes[i]; assert(n, "N:find inconsistent"); return n:find(
            s + BITS, h, k)
    end; return nil
end

--- @private Node method
local function node_iter_next(p, st)
    local slf = p; while true do
        if st.cg then
            local is, k, v = st.cg(st.cp, st.cs); st.cs = is; if is ~= nil then return st, k, v end; st.cg, st.cp = nil,
                nil; st.idx = st.idx + 1
        end; if st.idx <= #slf.nodes then
            local c = slf.nodes[st.idx]; assert(c and c.iter, "N:iter bad child"); local g, cp, cs = c:iter(); if g then
                st.cg, st.cp, st.cs =
                    g, cp, cs
            else
                st.idx = st.idx + 1
            end
        else
            return nil, nil, nil
        end
    end
end
function Node:iter() return node_iter_next, self, { idx = 1 } end

--- @private Node method: Recursive Merge logic restored
function Node:merge(shift, other_node, owner)
    if self == other_node then return self, 0 end; local other_mt = getmetatable(other_node)
    if other_mt == Node_mt then -- Node + Node merge
        local new_bitmap = self.bitmap; local merged_nodes = {}; local change_count = 0
        for i = 0, MASK do
            local b = b_lshift(1, i); local sh = b_band(self.bitmap, b) ~= 0; local oh = b_band(other_node.bitmap, b) ~=
                0; if sh and oh then
                local i1, i2 = idxFor(self.bitmap, b), idxFor(other_node.bitmap, b); local c1, c2 = self.nodes[i1],
                    other_node.nodes[i2]; assert(c1 and c2, "N+N nil child"); local mc, d = merge_nodes(c1, shift + BITS,
                    c2, owner); assert(mc, "merge nil"); table_insert(merged_nodes, mc); if mc ~= c1 then
                    change_count =
                        change_count + d
                end; new_bitmap = b_bor(new_bitmap, b)
            elseif sh then
                local i1 = idxFor(self.bitmap, b); local c1 = self.nodes[i1]; assert(c1, "N+N nil self c"); table_insert(
                    merged_nodes, c1); new_bitmap = b_bor(new_bitmap, b)
            elseif oh then
                local i2 = idxFor(other_node.bitmap, b); local c2 = other_node.nodes[i2]; assert(c2, "N+N nil other c"); table_insert(
                    merged_nodes, c2); new_bitmap = b_bor(new_bitmap, b); local sz = (getmetatable(c2) == CLeaf_mt) and
                    #c2.leaves or 1; change_count = change_count + sz
            end
        end
        if new_bitmap == self.bitmap and change_count == 0 then
            local s = (#merged_nodes == #self.nodes); if s then
                for i = 1, #merged_nodes do
                    if merged_nodes[i] ~= self.nodes[i] then
                        s = false; break
                    end
                end
            end
            if s then return self, 0 end
        end
        local r = copy_node_instance(owner, self); r.bitmap = new_bitmap; r.nodes = copy_nodes_array(merged_nodes); return
            r, change_count
    elseif other_mt == Leaf_mt or other_mt == CLeaf_mt then -- Node + Leaf/CLeaf merge
        local temp_owner = { _mutate = {} }; local node_copy = copy_node_instance(temp_owner, self); local delta = 0
        if other_mt == Leaf_mt then
            local next_n, upd = node_copy:assoc(shift, other_node.hash, other_node.key, other_node.val); delta = upd and
                0 or 1; node_copy = next_n
        else
            for _, leaf in ipairs(other_node.leaves) do
                local next_n, upd = node_copy:assoc(shift, leaf.hash, leaf.key, leaf.val); if not upd then
                    delta = delta +
                        1
                end; node_copy = next_n
            end
        end
        node_copy._mutate = nil; return node_copy, delta
    else
        error("Cannot merge Node with unknown type")
    end
end

implements_node(Node); -- }}}

-- Leaf Type {{{
--- @class Leaf HAMT Leaf Node (holds single key/value)
--- @field hash number Hash value of the key
--- @field key any The key stored in this leaf
--- @field val any The value stored in this leaf
--- @field _mutate table|nil Optional mutation token
Leaf = {}; Leaf_mt = { name = "Leaf", __index = Leaf };
--- @private Leaf Constructor
function LeafC(h, k, v) return setmetatable({ hash = h, key = k, val = v }, Leaf_mt) end

--- @private Leaf method
function Leaf:assoc(s, h, k, v)
    local o = self._mutate and self or nil; if h == self.hash then
        if k == self.key then return (v == self.val and self or LeafC(h, k, v)), true end; return
            CLeafC(h, { self, LeafC(h, k, v) }, o), false
    else
        return Node.create(s, self, h, k, v), false
    end
end

--- @private Leaf method
function Leaf:without(s, h, k)
    if h == self.hash and k == self.key then return nil end; return self
end

--- @private Leaf method
function Leaf:find(s, h, k)
    if h == self.hash and k == self.key then return self end; return nil
end

--- @private Leaf method
local function leaf_iter_next(p, st)
    if st.first then
        st.first = false; return st, p.key, p.val
    end; return nil, nil, nil
end
function Leaf:iter() return leaf_iter_next, self, { first = true } end

--- @private Leaf method: Recursive Merge logic restored
function Leaf:merge(shift, other_node, owner)
    if self == other_node then return self, 0 end; local other_mt = getmetatable(other_node)
    if other_mt == Leaf_mt then
        if self.hash == other_node.hash then
            if self.key == other_node.key then return other_node, 0 end; return CLeafC(self.hash, { self, other_node },
                owner), 1
        end; return Node.create(shift, self, other_node.hash, other_node.key, other_node.val), 1
    elseif other_mt == CLeaf_mt or other_mt == Node_mt then
        local temp_owner = { _mutate = {} }; local other_copy = copy_node_instance(temp_owner, other_node); local result_other, upd =
            other_copy:assoc(shift, self.hash, self.key, self.val); result_other._mutate = nil; local delta = upd and 0 or
            1; return
            result_other, delta
    else
        error("Cannot merge Leaf with unknown type")
    end
end

implements_node(Leaf); -- }}}

-- CLeaf Type {{{
--- @class CLeaf HAMT Collision Leaf Node (holds multiple Leaves with same hash)
--- @field hash number Hash value shared by all colliding keys
--- @field leaves Leaf[] Array of leaf nodes with the same hash
--- @field _mutate table|nil Optional mutation token
CLeaf = {}; CLeaf_mt = { name = "CLeaf", __index = CLeaf }
local function findLeafIndex(ls, k)
    for i, l in ipairs(ls) do if l.key == k then return i end end; return nil
end
--- @private CLeaf Constructor
function CLeafC(h, ls, o)
    assert(type(ls) == 'table', "Bad CLeaf"); local inst = { hash = h, leaves = copy_nodes_array(ls) }; if o and o._mutate then
        inst._mutate =
            o._mutate
    end; return setmetatable(inst, CLeaf_mt)
end

--- @private CLeaf method
function CLeaf:assoc(s, h, k, v)
    local o = self._mutate and self or nil; if h == self.hash then
        local idx = findLeafIndex(self.leaves, k); if idx then
            if self.leaves[idx].val == v then return self, true end; local nl = copy_nodes_array(self.leaves); nl[idx] =
                LeafC(h, k, v); return CLeafC(h, nl, o), true
        end; local nl = copy_nodes_array(self.leaves); table_insert(nl, LeafC(h, k, v)); return CLeafC(h, nl, o), false
    else
        local nl = LeafC(h, k, v); local fc = b_band(b_rshift(self.hash, s), MASK); local fn = b_band(b_rshift(h, s),
            MASK); if fc == fn then
            local deeper_node = Node.create(s + BITS, self, h, k, v); if deeper_node == nil then return nil, false end; return
                NodeC { bitmap = mask(h, s), nodes = { deeper_node }, shift = s }, false
        else
            local bm = b_bor(mask(self.hash, s), mask(h, s)); local ns = (fc < fn) and { self, nl } or { nl, self }; return
                NodeC { bitmap = bm, nodes = ns, shift = s }, false
        end
    end
end

--- @private CLeaf method
function CLeaf:without(s, h, k)
    local o = self._mutate and self or nil; if h ~= self.hash then return self end; local idx = findLeafIndex(
        self.leaves, k); if not idx then return self end; local len = #self.leaves; if len <= 1 then return nil end; if len == 2 then
        return
            self.leaves[(idx == 1) and 2 or 1]
    end; local nl = copy_nodes_array(self.leaves); table_remove(nl, idx); return
        CLeafC(h, nl, o)
end

--- @private CLeaf method
function CLeaf:find(s, h, k)
    if h ~= self.hash then return nil end; local idx = findLeafIndex(self.leaves, k); return idx and self.leaves[idx] or
        nil
end

--- @private CLeaf method
local function cleaf_iter_next(p, st)
    local slf = p; if st.idx <= #slf.leaves then
        local l = slf.leaves[st.idx]; st.idx = st.idx + 1; return st, l.key, l.val
    end; return nil, nil, nil
end
function CLeaf:iter() return cleaf_iter_next, self, { idx = 1 } end

--- @private CLeaf method: Recursive Merge logic restored
function CLeaf:merge(shift, other_node, owner)
    if self == other_node then return self, 0 end; local other_mt = getmetatable(other_node)
    if other_mt == CLeaf_mt then -- CLeaf + CLeaf merge
        if self.hash ~= other_node.hash then
            local e = NodeC { bitmap = 0, nodes = {}, shift = shift }; local n1, c1 = merge_nodes(e, shift, self, owner); local n2, c2 =
                merge_nodes(n1, shift, other_node, owner); return n2, c1 + c2
        end
        local temp_owner = { _mutate = {} }; local current_cleaf = copy_node_instance(temp_owner, self); local delta = 0
        for _, leaf in ipairs(other_node.leaves) do
            local next_c, upd = current_cleaf:assoc(shift, leaf.hash, leaf.key, leaf.val); if not upd then
                delta = delta +
                    1
            end; current_cleaf = next_c
        end
        current_cleaf._mutate = nil; if #current_cleaf.leaves == 0 then return nil, delta - #self.leaves end; if #current_cleaf.leaves == 1 then
            return
                current_cleaf.leaves[1], delta - (#self.leaves - 1)
        end; return current_cleaf, delta
    elseif other_mt == Leaf_mt then -- CLeaf + Leaf merge
        if self.hash ~= other_node.hash then
            local e = NodeC { bitmap = 0, nodes = {}, shift = shift }; local n1, c1 = merge_nodes(e, shift, self, owner); local n2, c2 =
                merge_nodes(n1, shift, other_node, owner); return n2, c1 + c2
        end
        local result_node, upd = self:assoc(shift, other_node.hash, other_node.key, other_node.val); local delta = upd and
            0 or 1
        local final_delta = delta; if getmetatable(result_node) == Leaf_mt then final_delta = delta - (#self.leaves - 1) end; if result_node == nil then
            final_delta =
                delta - #self.leaves
        end; return result_node, final_delta
    elseif other_mt == Node_mt then -- CLeaf + Node merge
        local temp_owner = { _mutate = {} }; local node_copy = copy_node_instance(temp_owner, other_node); local delta = 0
        for _, leaf in ipairs(self.leaves) do
            local next_n, upd = node_copy:assoc(shift, leaf.hash, leaf.key, leaf.val); if not upd then delta = delta + 1 end; node_copy =
                next_n
        end
        node_copy._mutate = nil; return node_copy, delta
    else
        error("Cannot merge CLeaf with unknown type")
    end
end

implements_node(CLeaf); -- }}}

-- [MERGE RESTORED] Generic merge dispatcher function
function merge_nodes(node1, shift, node2, owner)
    if node1 == nil then
        local c2 = 0; if node2 then
            local mt2 = getmetatable(node2); if mt2 == Leaf_mt then
                c2 = 1
            elseif mt2 == CLeaf_mt then
                c2 = #node2
                    .leaves
            elseif mt2 == Node_mt then
                c2 = #node2.nodes
            else
                if node2 ~= Hash.EMPTY.root then
                    error(
                        "merge_nodes: Unknown node2")
                end
            end
        end
        return node2, c2
    end
    if node2 == nil then return node1, 0 end
    local mt1 = getmetatable(node1); assert(mt1 and mt1.__index and mt1.__index.merge, "merge_nodes: Node1 lacks merge")
    return node1:merge(shift, node2, owner) -- Dispatch to node1's merge method
end

-- }}} -- End Nodes Definition and Implementation


-- {{{ Hashmap Public Interface Methods

--- Returns the number of key-value pairs in the hashmap.
-- @return number The number of elements.
function Hash:len() return self.count end; mt.__len = Hash.len

--- Returns a new hashmap with the key-value pair associated.
-- @param key The key to associate.
-- @param val The value to associate.
-- @return Hashmap A new Hashmap instance.
function Hash:assoc(key, val)
    assert(self and self.root, "H:assoc invalid self"); local h = hashcode_func(key)
    local nr, upd = self.root:assoc(0, h, key, val)
    if nr == nil then
        if self.count == 1 and not upd then return Hash.EMPTY end; assert(false, "H:assoc nil root")
    end
    if nr == self.root then return self end
    local nc = self.count + (upd and 0 or 1); local new_map_data = { count = nc, root = nr }; if self._mutate then
        new_map_data._mutate =
            self._mutate
    end
    return Hmap(new_map_data)
end

--- Gets the value associated with a key.
-- @param key The key to look up.
-- @return The associated value, or `nil` if not found.
function Hash:get(key)
    assert(self and self.root, "H:get invalid self"); local h = hashcode_func(key); local e = self.root:find(0, h, key); return
        e and e.val
end

--- Returns a new hashmap without the association for the given key.
-- @param key The key to dissociate.
-- @return Hashmap A new Hashmap instance, the original map, or EMPTY.
function Hash:dissoc(key)
    assert(self and self.root, "H:dissoc invalid self"); local h = hashcode_func(key); local nr = self.root:without(0, h,
        key); if nr == self.root then return self end; if nr == nil then return Hash.EMPTY end; local new_map_data = {
        count =
            self.count - 1,
        root = nr
    }; if self._mutate then new_map_data._mutate = self._mutate end; return Hmap(new_map_data)
end

--- Returns a new hashmap containing all keys from `self` and `other`. Values from `other` take precedence.
-- Uses recursive node merging strategy.
-- @param other Hashmap The other hashmap instance to merge with.
-- @return Hashmap A new Hashmap instance representing the merged result.
function Hash:merge(other)
    assert(self and self.root, "H:merge invalid self"); assert(other and getmetatable(other) == mt,
        "H:merge invalid other")
    if not other or other == Hash.EMPTY or other.count == 0 then return self end
    if self == Hash.EMPTY or self.count == 0 then return other end
    if self == other then return self end
    local owner = self._mutate and self or nil
    local _, d -- [FIX] Declare local _ for Lua 5.1
    local mr, _ = merge_nodes(self.root, 0, other.root, owner)
    if mr == self.root then return self end
    local nc = 0; if mr then
        local iFn, iP, iS = mr:iter(); if iFn then
            repeat
                iS, _, _ = iFn(iP, iS); if iS then nc = nc + 1 end
            until iS == nil
        end
    end -- Recalculate count accurately
    if nc == 0 then return Hash.EMPTY end
    local new_map_data = { count = nc, root = mr }; if self._mutate then new_map_data._mutate = self._mutate end
    return Hmap(new_map_data)
end

--- Returns a raw iterator function (`gen, param, state`). Use `pairs()` for loops.
-- @return function iterator_func
-- @return Hashmap map_instance
-- @return table initial_state
function Hash:iter()
    assert(self and self.root, "H:iter invalid self"); return self.root:iter()
end

--- Returns a standard Lua `for k, v in ...` iterator function. Order is not guaranteed.
-- @return function The iterator closure.
function Hash:pairs()
    assert(self and self.root, "H:pairs invalid self"); local gen, p, s = self.root:iter(); if not gen then return function() return nil end end; local function closure()
        local ns, k, v = gen(p, s); s = ns; return k, v
    end; return closure
end; mt.__pairs = Hash.pairs

--- Constructs a read-only table view of the hashmap.
-- @return table A read-only table view.
function Hash:asTable()
    local slf = self; return setmetatable({},
        {
            __newindex = function(_, k) error("Read-only view key: " .. tostring(k)) end,
            __index = function(_, k)
                return
                    slf:get(k)
            end,
            __pairs = function() return slf:pairs() end,
            __len = function() return slf:len() end
        })
end

-- Transient/Mutability Handling {{{

--- Returns a mutable (transient) version of this hashmap.
-- @return Hashmap A new Hashmap instance marked as mutable.
function Hash:asMutable()
    local owner_token = {} -- Use table as token
    local mutable_data = { count = self.count, root = self.root, _mutate = owner_token }
    return setmetatable(mutable_data, mt)
end

--- Returns an immutable (persistent) version of this hashmap.
-- @return Hashmap An immutable Hashmap instance.
function Hash:asImmutable()
    if self._mutate then self._mutate = nil end
    return self
end

--- Performs batch modifications efficiently using a transient hashmap.
-- @tparam function fn Function to apply: `function(mutable_map) -> modified_map | nil`
-- @return Hashmap A persistent hashmap reflecting the changes made by `fn`.
function Hash:withMutations(fn)
    local mut = self:asMutable(); local res = fn(mut); if res and res.asImmutable then
        return res:asImmutable()
    elseif res == nil and mut then
        return
            mut:asImmutable()
    else
        return self:asImmutable()
    end
end

-- }}} End Transient Handling

-- Define the EMPTY map instance (singleton)
local function empty_iter_next() return nil, nil, nil end
--- The canonical empty Hashmap instance. Read-only.
Hash.EMPTY = Hmap { count = 0, root = setmetatable({}, { name = "EmptyRoot", __index = {
    assoc = function(_, s, h, k, v) return LeafC(h, k, v) end,
    without = function(slf) return slf end,
    find = function() return nil end,
    iter = function() return empty_iter_next, nil, nil end,
    merge = function(_, s, o, own)
        local _, d = merge_nodes(nil, s, o, own); return o, d
    end -- Empty:merge(Other) -> Other
} }) }
-- Verify EmptyRoot implements the node interface (including merge now)
implements_node(Hash.EMPTY.root)

return Hash
-- }}} End Hashmap Public Interface Methods
