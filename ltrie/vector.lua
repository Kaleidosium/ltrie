--- An immutable vector datatype, modeled after Clojure's PersistentVector.
--  It can be used to store sequential data, much like Lua tables:
--
--      local my_vector = Vector.from('a', 'b', 'c')
--      print(my_vector:get(2)) -- 'c'
--
--  But because they are persistent, modifications create a new vector instead
--  of changing the old one:
--
--      local my_new_vector = my_vector:set(2, 'd')
--      print(my_new_vector:get(2)) -- 'd'
--      print(my_vector:get(2))     -- still 'c'
--
--  Vectors are dense, ordered, and indexed-by-one, meaning a vector will never
--  have an element whose index doesn't fall in between `[1 .. v:len()]`.
--
--  `nil` is a valid element, however, so a vector like:
--
--      Vector.of(1, nil, nil, 4)
--
--  has a size of four, and iterating through it
--  will include the nil values.
--
--  @module Vector

-- Implementation Notes
-- ====================
--
-- A good blogpost explaining the structure's implementation:
--
-- <http://hypirion.com/musings/understanding-persistent-vector-pt-1>
--
-- My reference code was this particular commit:
--
-- <http://git.io/vT7zG>
--
-- To match Lua's index-by-one semantics I had to introduce an offset or two.
-- Every line I've done that on is marked with a +1 or -1 comment.

local function try(...)
    local ok, err = pcall(...)
    if not ok then return nil end
    return err
end
-- Attempt to load bit operations library (bit32 preferred)
local b      = try(require, 'bit32') or try(require, 'bit') or error("No bitop lib found")

local BITS   = 5 -- Number of bits per trie level (log2(WIDTH))
local WIDTH  = 32 -- Width of trie nodes (2^BITS)
local MASK   = 31 -- Bitmask for indexing within a node (WIDTH - 1)

--- @alias Vector table Metatable for Vector instances
local Vector = {}

local mt     = {
    __index = Vector,
}

-- Internal constructor for Vector instances
local function Vec(data)
    assert(data.count ~= nil) -- Use ~= nil check to allow count = 0
    assert(data.shift ~= nil)
    assert(data.root)
    assert(data.tail)
    return setmetatable(data, mt)
end

-- The canonical empty vector instance
local EMPTY = Vec {
    count = 0,
    shift = BITS,
    root  = {}, -- Empty table represents the empty root node
    tail  = {},
}

--- Creates a vector containing the elements provided by the given iterator.
-- @tparam function gen The generator function of the iterator
-- @tparam any state The initial state for the iterator
-- @tparam any initial The initial value for the iterator
-- @usage Vector.from(ipairs {1, 2, 3, 4})
function Vector.from(gen, state, initial)
    local r = EMPTY:asMutable()
    -- IMPORTANT: Use the vector returned by conj in the loop
    for _, v in gen, state, initial do
        r = r:conj(v)
    end
    r:asImmutable()
    return r
end

--- Creates a vector containing the arguments.
-- @param ... the arguments to include
-- @usage Vector.of(1, 2, 3, 4)
function Vector.of(...)
    local r = EMPTY:asMutable()
    -- IMPORTANT: Use the vector returned by conj in the loop
    for i = 1, select('#', ...) do
        r = r:conj(select(i, ...))
    end
    r:asImmutable()
    return r
end

--- Checks to see if given object is a vector.
-- @param o anything
-- @treturn bool `true` if Vector, false if not
function Vector.is_vector(o)
    return getmetatable(o) == mt
end

--- @type Vector

--- Returns the number of elements contained in the vector.
-- In lua 5.2 and up, `#vector` can be used as a shortcut.
--
-- @complexity O(1)
-- @usage Vector.of(1, 2, 3):len() == 3
function Vector:len()
    return self.count
end

mt.__len = Vector.len -- Enable the # operator

-- Helper to apply the bitmask
local function mask(i)
    return b.band(i, MASK)
end

-- Calculates the index where the tail starts (or 0 if count < WIDTH)
local function tailoff(trie)
    if trie.count <= WIDTH then -- Use <= to handle the case where count == WIDTH exactly
        return 0
    else
        -- Calculate the start index of the last full node block
        local last_idx = trie.count - 1 -- 0-based index of the last element
        -- Effectively rounds down `last_idx` to the nearest multiple of WIDTH
        return b.lshift(b.rshift(last_idx, BITS), BITS)
    end
end

-- Sentinel value for out-of-bounds access in arrayFor
local OOB = {}

-- Finds the node (table) containing the element at the given 0-based index
local function arrayFor(trie, idx)
    -- Check bounds (0-based index)
    if not (idx >= 0 and idx < trie.count) then
        return OOB -- Out of bounds
    end

    -- Check if the index falls within the tail
    if idx >= tailoff(trie) then
        return trie.tail
    end

    -- Traverse the trie from the root
    local node = trie.root
    local level = trie.shift
    while level > 0 do
        -- Calculate the index within the current node (1-based for Lua tables)
        local node_idx = mask(b.rshift(idx, level)) + 1 -- +1 for 1-based Lua table index
        node = node[node_idx]
        -- Should not encounter nil nodes in a valid path for existing elements
        if not node then return OOB end -- Path is broken or index is invalid
        level = level - BITS
    end
    return node -- Return the leaf node containing the element
end

--- Get a value by index. Vector indexes start at one.
--
-- @complexity O(log32 n)
-- @tparam int idx the index (1-based)
-- @return the value, or `nil` if not found or index out of bounds
-- @usage Vector.of(1, 2, 3):get(1) == 1
function Vector:get(idx)
    if idx < 1 or idx > self.count then return nil end -- Explicit bounds check for 1-based index
    local zero_based_idx = idx - 1                     -- -1 Convert to 0-based for internal logic

    local node = arrayFor(self, zero_based_idx)
    if node == OOB then return nil end -- Index was out of bounds or path error

    -- Calculate index within the final node (1-based for Lua tables)
    local final_idx = mask(zero_based_idx) + 1 -- +1 for 1-based Lua table index
    return node[final_idx]
end

-- Note: Using Vector:get directly for __index can be confusing as __index
-- usually looks for methods. Keeping mt.__index = Vector is standard.
-- mt.__index = Vector.get -- This would make `vec[i]` call `vec:get(i)`

-- Iterator function for ipairs
local function iter_impl(vec, idx)
    -- Check if vec or vec.count is nil (Defensive check for subvec issue)
    if not vec or vec.count == nil then
        -- This indicates an issue with the caller (e.g., subvec)
        -- Return nil to stop iteration gracefully, though the root cause is external.
        return nil
    end
    idx = idx + 1
    if idx <= vec.count then
        return idx, vec:get(idx) -- Return 1-based index and value
    end
    -- No more elements
    return nil
end

--- Iterate through the vector, from beginning to end (1-based index).
-- Returns `index, value` consistent with Lua's `ipairs`.
-- @usage for i, v in my_vector:ipairs() do print(i, v) end
function Vector:ipairs()
    return iter_impl, self, 0
end

mt.__ipairs = Vector.ipairs -- Enable ipairs(vector)

--- Unpack the vector elements. Equivalent to `table.unpack` for tables.
-- Be cautious with very large vectors, as this creates many return values.
-- @usage local a, b, c = Vector.of('a', 'b', 'c'):unpack()
function Vector:unpack()
    local l = self:len()
    if l == 0 then return end -- Nothing to unpack

    local results = {}
    for i = 1, l do
        results[i] = self:get(i)
    end
    -- Use standard library unpack if available, otherwise provide fallback
    local unpack_func = table.unpack or unpack
    return unpack_func(results, 1, l)
end

-- Creates a new path (branch) in the trie down to a given level,
-- placing the node at the bottom. Used when expanding the trie depth.
local function newPath(level, node)
    if level == 0 then
        return node -- Base case: return the node itself
    end
    -- Create a new parent node containing the recursively created path
    local r = {}
    r[1] = newPath(level - BITS, node) -- Place the path at the first index
    return r
end

-- Creates a potentially mutable copy of a table (node or vector).
-- If the owner vector is mutable and the table belongs to the same mutation,
-- return the table directly. Otherwise, create a shallow copy.
local function copy(owner, tbl)
    -- Check if owner allows mutation and if tbl is part of the same mutation
    if owner._mutate and tbl._mutate == owner._mutate then
        return tbl -- It's safe to mutate this table directly
    end

    -- Create a shallow copy
    local t = {}
    -- Copy key-value pairs
    for k, v in pairs(tbl) do
        t[k] = v
    end

    -- If the owner is mutable, mark the new copy as belonging to its mutation
    if owner._mutate then
        t._mutate = owner._mutate
    end
    -- Preserve the metatable if the original table had one
    return setmetatable(t, getmetatable(tbl))
end


-- Pushes the old tail down into the trie structure when the tail becomes full.
-- Returns the new root node.
local function pushTail(self, level, parent, tailNode)
    -- Create a potentially mutable copy of the parent node
    local editable_parent = copy(self, parent)
    -- Calculate the index within the parent node where the new branch should go (0-based logic -> 1-based index)
    -- self.count - 1 is the 0-based index of the *last element of the old tail*
    local subidx = mask(b.rshift(self.count - 1, level)) + 1 -- +1 for 1-based Lua table index

    local nodeToInsert
    if level == BITS then
        -- Base case: parent is a leaf level, insert the tail node directly
        nodeToInsert = tailNode
    else
        -- Recursive case: Need to go deeper
        local childNode = editable_parent[subidx] -- Read from the editable copy
        if childNode then
            -- Child exists, recurse down
            nodeToInsert = pushTail(self, level - BITS, childNode, tailNode)
        else
            -- No child node exists, create a new path for the tail node
            nodeToInsert = newPath(level - BITS, tailNode)
        end
    end

    -- Insert the new/updated node into the copied parent
    editable_parent[subidx] = nodeToInsert
    return editable_parent
end

--- Returns a new vector with val appended to the end.
-- @complexity Amortized O(1), Worst Case O(log32 n)
-- @param val the value to append
-- @usage Vector.of(1, 2):conj(3) == Vector.of(1, 2, 3)
function Vector:conj(val)
    local idx = self.count -- 0-based index for the new element

    -- Check if there is room in the tail
    if self.count - tailoff(self) < WIDTH then
        -- Room in tail: Copy tail, append value, update vector state
        local newTail = copy(self, self.tail)
        newTail[#newTail + 1] = val -- More direct append

        -- Create a potentially mutable copy of the vector itself
        local r = copy(self, self)
        r.count = self.count + 1
        r.tail = newTail
        return Vec(r) -- Ensure metatable is set
    end

    -- Tail is full: Push tail into the trie, start new tail
    local newRoot
    local tailNode = copy(self, self.tail) -- Copy the tail to become a trie node
    local newShift = self.shift

    -- Check if the root trie needs to expand (increase depth)
    -- Condition based on reference implementation: (cnt >> BITS) > (1 << shift)
    -- Use current count (idx) as cnt is the index of the element being added.
    -- (FIXED: Apply corrected overflow condition)
    if b.rshift(idx, BITS) > b.lshift(1, self.shift) then
        -- Root overflow: Create a new root, increase shift
        newRoot = {}
        newRoot[1] = self.root                     -- Old root becomes first child
        newRoot[2] = newPath(self.shift, tailNode) -- New path for the old tail becomes second child
        newShift = self.shift + BITS
    else
        -- No overflow: Push the tail node into the existing root structure
        newRoot = pushTail(self, self.shift, self.root, tailNode)
    end

    -- Create the new vector state
    local r = copy(self, self)
    r.count = self.count + 1
    r.shift = newShift
    r.root  = newRoot
    r.tail  = { val } -- Start a new tail with the appended value
    return Vec(r)   -- Ensure metatable is set
end

-- Recursively traverses the trie to set a value at a specific index.
-- Returns the modified node at the current level.
local function doAssoc(self, level, node, idx, val)
    local editable_node = copy(self, node) -- Make copy first

    if level == 0 then
        -- Base case: Reached the leaf node level
        local leaf_idx = mask(idx) + 1 -- +1 for 1-based Lua table index
        editable_node[leaf_idx] = val
    else
        -- Recursive case: Go deeper
        local node_idx = mask(b.rshift(idx, level)) + 1 -- +1 for 1-based Lua table index
        local childNode = editable_node[node_idx]       -- <<< FIXED: Read from the editable_node copy
        if not childNode then
            -- This should still not happen for a valid in-bounds assoc if structure is correct
            error("Internal error: Path node missing in doAssoc for index " ..
            (idx + 1) .. " at level " .. level .. " node_idx " .. node_idx)
        end
        -- Recurse using the childNode found in the editable copy
        editable_node[node_idx] = doAssoc(self, level - BITS, childNode, idx, val)
    end
    return editable_node
end


--- Returns a new vector such that `vector:get(idx) == val`.
-- Index must be between 1 and vector:len() (inclusive).
-- Use `conj` to add a new element at the end.
-- @complexity O(log32 n)
-- @tparam int idx the index to set (1-based)
-- @param val the value to set
-- @usage Vector.of(0, 0, 0):assoc(2, 'a') == Vector.of(0, 'a', 0)
function Vector:assoc(idx, val)
    -- Bounds check (1-based index)
    if idx < 1 or idx > self.count then
        error("Index out of bounds: " .. tostring(idx) .. " for vector of size " .. self.count)
    end

    local zero_based_idx = idx - 1 -- -1 Convert to 0-based for internal logic

    -- Check if the index is in the tail
    if zero_based_idx >= tailoff(self) then
        -- Modify the tail
        local newTail = copy(self, self.tail)
        local tail_idx = mask(zero_based_idx) + 1 -- +1 for 1-based Lua table index
        newTail[tail_idx] = val

        local r = copy(self, self)
        r.tail = newTail
        return Vec(r) -- Ensure metatable is set
    end

    -- Modify the trie structure
    local r = copy(self, self)
    r.root = doAssoc(self, self.shift, self.root, zero_based_idx, val)
    return Vec(r) -- Ensure metatable is set
end

-- Alias set to assoc
Vector.set = Vector.assoc

-- Recursively removes the path corresponding to the last element of the *trie part*
-- (not the tail part) and prunes empty branches. Returns the modified node or nil if pruned.
-- Operates on the state *before* the pop conceptually happens (i.e., uses self.count - 2).
local function popTail(self, level, node)
    -- Calculate the index within the node corresponding to the element *before* the last one in the trie
    local zero_based_idx_to_keep = self.count - 2                    -- 0-based index of the element that will become the last in the trie
    local subidx = mask(b.rshift(zero_based_idx_to_keep, level)) + 1 -- +1 for 1-based Lua table index

    if level > BITS then
        -- Recursive case: Go deeper
        local childNode = node[subidx]
        if not childNode then
            -- This shouldn't happen if count > 1 and we are not in the tail
            -- If it does, maybe the structure is already broken? Return node unchanged.
            return node
        end
        local newChild = popTail(self, level - BITS, childNode)

        -- Pruning logic: If the recursive call pruned the child entirely,
        -- and it was the *only* child remaining up to that point (subidx == 1), prune this node too.
        if newChild == nil and subidx == 1 then
            return nil -- Prune this node
        else
            -- Otherwise, update the child in a copy of the current node
            local r = copy(self, node)
            r[subidx] = newChild -- Update with potentially pruned child
            -- Clean up subsequent indices if they exist (they shouldn't in a canonical trie after a pop)
            for i = subidx + 1, WIDTH do r[i] = nil end
            return r
        end
        -- Base case (level == BITS): Check if the element to keep is the *first* in this leaf node.
    elseif subidx == 1 then
        -- If the element to keep is the first one (index 1), it means this node becomes empty
        -- after the pop (relative to the trie path being considered). Signal to prune by returning nil.
        return nil
    else
        -- Element to keep is not the first. Keep this node, but remove elements after subidx.
        local r = copy(self, node)
        -- Remove elements after the one we are keeping ( conceptually )
        for i = subidx + 1, WIDTH do r[i] = nil end
        return r
    end
end


--- Returns a new vector with the last value removed.
-- @complexity Amortized O(1), Worst Case O(log32 n)
-- @usage Vector.of(1, 2, 3):pop() == Vector.of(1, 2)
-- @return The new vector with the last element removed.
function Vector:pop()
    if self.count == 0 then
        error("Can't pop from empty vector")
    elseif self.count == 1 then
        -- Popping the last element returns the canonical empty vector
        return EMPTY
    end

    -- Check if the element to remove is in the tail (and tail has more than 1 element)
    if self.count - tailoff(self) > 1 then
        -- Simple case: Just remove the last element from the tail
        local newTail = copy(self, self.tail)
        newTail[#newTail] = nil -- More direct removal (doesn't resize table like table.remove)

        local r = copy(self, self)
        r.count = self.count - 1
        r.tail = newTail
        return Vec(r) -- Ensure metatable is set
    end

    -- Complex case: Last element is the only element in the tail.
    -- Need to pop from the trie and make the last node of the trie the new tail.

    -- Find the node that will become the new tail (node containing index count - 2)
    local newTailNode = arrayFor(self, self.count - 2)
    if newTailNode == OOB then
        error("Internal error: Could not find node for new tail in pop")
    end
    -- Make a mutable copy of the node that will become the new tail
    local newTail = copy(self, newTailNode)

    -- Remove the path to the old tail node from the trie structure
    local newRoot = popTail(self, self.shift, self.root)
    local newShift = self.shift

    -- Check if the root became empty or requires shrinking
    if newRoot == nil then
        -- Trie part became completely empty
        newRoot = EMPTY.root
        -- Check if the root can be collapsed (only one child at the top level)
    elseif self.shift > BITS and newRoot[1] and newRoot[2] == nil then -- Ensure child 1 exists before checking child 2
        -- Root has only one child (at index 1), collapse the root level
        newRoot = newRoot[1]                                           -- The single child becomes the new root
        newShift = self.shift - BITS
    end

    -- Create the new vector state
    local r = copy(self, self)
    r.count = self.count - 1
    r.shift = newShift
    r.root  = newRoot
    r.tail  = newTail -- Assign the copied node as the new tail
    return Vec(r)     -- Ensure metatable is set
end

--- Returns a transient mutable copy of the vector.
-- Operations on the transient vector may modify it in place.
-- The original vector remains unchanged.
-- @nodiscard The returned mutable vector should be used.
function Vector:asMutable()
    -- Create a unique table to identify this mutation session
    local mutation_id = {}
    local mutable_copy = copy({ _mutate = mutation_id }, self)
    -- Ensure the nodes are also marked mutable for the first level of edits
    mutable_copy.root = copy(mutable_copy, mutable_copy.root)
    mutable_copy.tail = copy(mutable_copy, mutable_copy.tail)
    mutable_copy._mutate = mutation_id -- Ensure the top-level vector itself is marked
    return mutable_copy
end

--- Makes a transient vector persistent (immutable).
-- This should be called on the result of `asMutable` or within `withMutations`.
function Vector:asImmutable()
    self._mutate = nil -- Remove the mutation marker
    -- Note: This doesn't recursively clean markers from nodes, relying on
    -- the copy-on-write mechanism to isolate subsequent changes.
end

--- Performs batch operations efficiently using a transient mutable vector.
-- The function `fn` receives a mutable version of the vector.
-- The vector returned by `fn` (or the modified mutable vector if `fn` returns nil)
-- is made immutable and returned by `withMutations`.
-- @tparam function fn A function that takes a mutable vector and returns a vector (or nil).
-- @return A new persistent vector reflecting the changes made by `fn`.
-- @usage
-- local vec = Vector.of(1, 2, 3)
-- local new_vec = vec:withMutations(function(mut)
--   mut = mut:assoc(1, 10)
--   mut = mut:conj(40)
--   mut = mut:pop()
--   return mut -- Return the modified mutable vector
-- end)
-- -- new_vec is Vector.of(10, 2, 3)
function Vector:withMutations(fn)
    local mut = self:asMutable()
    local result_vec = fn(mut) -- Call the user function with the mutable vector

    -- If the function didn't explicitly return a vector, assume it modified 'mut' in place
    if result_vec == nil then
        result_vec = mut
    end

    -- Ensure the final result is immutable
    -- Check if it's the *same* mutable vector instance we started with
    if Vector.is_vector(result_vec) and result_vec._mutate == mut._mutate then
        result_vec:asImmutable()
    elseif Vector.is_vector(result_vec) then
        -- If fn returned a *different* vector, ensure it's immutable too
        -- (though this is less common for withMutations)
        result_vec:asImmutable()
    end

    return result_vec
end

-- Return the Vector module table
return Vector
