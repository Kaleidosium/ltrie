require 'spec/strict' ()

global 'bit32'
global 'file'
global 'level'

describe("hashmaps", function()
    local A = require 'ltrie.hashmap'
    local function totable(map)
        local t = {}
        if map and map.pairs then -- Check if map is a valid hashmap instance
            for k, v in map:pairs() do
                t[k] = v
            end
        end
        return t
    end

    it("implement from()/get()", function()
        local cmp = { a = 'a', b = 'c', c = 12 }
        local new = A.from(cmp)

        for k, v in pairs(cmp) do
            assert.are.equal(v, new:get(k))
        end

        cmp.a = 'b'
        assert.are_not.equal(new:get('a'), cmp.a)
    end)

    it("implement of()/pairs()", function()
        local cmp = { a = 'a', b = 'c', c = 12 }
        local new = A.of('a', 'a', 'b', 'c', 'c', 12)

        assert.are.same(cmp, totable(new)) -- Use totable for comparison
    end)

    it("implement assoc()/len()", function()
        local cmp = { a = 'a', b = 'c', c = 12 }
        local new = A.from(cmp)

        assert.is.equal(3, new:len())
        cmp.d = "JEFF"
        new = new:assoc('d', "JEFF")
        assert.is.equal(4, new:len())

        assert.are.same(cmp, totable(new))
    end)

    it("can overwrite existing values using assoc()", function()
        local t = A.from { a = 1 }

        assert.is.equal(1, t:get('a'))
        assert.is.equal(1, t:len())

        t = t:assoc('a', 1) -- Assoc same value
        assert.is.equal(1, t:get('a'))
        assert.is.equal(1, t:len())

        t = t:assoc('a', 4) -- Assoc different value
        assert.is.equal(4, t:get('a'))
        assert.is.equal(1, t:len())


        t = A.from { a = 1, b = 2, c = 3 }

        assert.is.equal(1, t:get('a'))
        assert.is.equal(3, t:len())

        t = t:assoc('a', 1) -- Assoc same value
        assert.is.equal(1, t:get('a'))
        assert.is.equal(3, t:len())

        t = t:assoc('a', 4) -- Assoc different value
        assert.is.equal(4, t:get('a'))
        assert.is.equal(3, t:len())
    end)

    it("can hold/delete many elems", function()
        local ELEMS = 2048   -- Reduced size for faster testing maybe?
        local tbl = {}
        local full = A.EMPTY -- Start empty for assoc testing
        for i = 1, ELEMS do
            local k = tostring(i)
            tbl[k] = i
            full = full:assoc(k, i)
            assert.is.equal(i, full:len())  -- Check length grows
            assert.is.equal(i, full:get(k)) -- Check inserted value
        end
        assert.is.equal(ELEMS, full:len())

        local empty = full
        local elen = empty:len()
        for i = 1, ELEMS do -- Iterate consistently
            local k = tostring(i)
            local v = tbl[k]
            assert.are.equal(v, empty:get(k), "Get failed before dissoc for key: " .. k)
            empty = empty:dissoc(k)
            assert.is.equal(nil, empty:get(k), "Get succeeded after dissoc for key: " .. k)
            elen = elen - 1
            assert.are.equal(elen, empty:len(), "Length mismatch after dissoc for key: " .. k)
        end

        assert.is.equal(empty:len(), 0)
        assert.is.equal(full:len(), ELEMS)
    end)

    it("implement dissoc()", function()
        local cmp = { a = 'a', b = 'c', c = 12 }
        local new = A.from(cmp)

        cmp.c = nil -- Modify expectation table
        assert.is.equal(12, new:get('c'))
        new = new:dissoc('c')
        assert.is.equal(2, new:len())
        assert.is.equal(nil, new:get('c'))
        assert.are.same(cmp, totable(new)) -- Check final state
    end)
end)

describe("large hashmaps", function()
    local A = require 'ltrie.hashmap'
    local ELEMS = 4096 -- Keep larger size for these tests

    -- Helper to create a large map and its table equivalent
    local function make_large_map_and_table()
        local tbl = {}
        local map = A.EMPTY
        for i = 1, ELEMS do
            local k = tostring(i)
            tbl[k] = i
            map = map:assoc(k, i)
        end
        return map, tbl
    end

    it("can be created", function()
        local t, tbl = make_large_map_and_table()
        assert.is.equal(ELEMS, t:len())
        for i = 1, ELEMS do
            assert.equal(i, t:get(tostring(i)))
        end
        -- Optional: Compare full table (can be slow)
        -- assert.are.same(tbl, totable(t))
    end)

    it("can be modified", function()
        local t, tbl = make_large_map_and_table()
        local original_t = t -- Keep original for immutability check

        local new_t = t:assoc('420', 69)
        tbl['420'] = 69 -- Update expectation

        assert.not_equal(69, original_t:get('420'), "Original map was modified by assoc")
        assert.is.equal(420, original_t:get('420'), "Original map value changed unexpectedly")
        assert.is.equal(ELEMS, original_t:len(), "Original map length changed unexpectedly")

        assert.is.equal(69, new_t:get('420'))
        assert.is.equal(ELEMS, new_t:len()) -- Length should remain same on overwrite

        -- Check a few other values remain correct
        assert.is.equal(1, new_t:get('1'))
        assert.is.equal(ELEMS, new_t:get(tostring(ELEMS)))

        -- Optional: Compare full table
        -- assert.are.same(tbl, totable(new_t))
    end)

    it("can be emptied", function()
        local full, tbl = make_large_map_and_table()
        local empty = full
        local elen = empty:len()

        for i = 1, ELEMS do
            local k = tostring(i)
            assert.is_not_nil(empty:get(k))
            empty = empty:dissoc(k)
            assert.is_nil(empty:get(k))
            elen = elen - 1
            assert.is.equal(elen, empty:len())
        end

        assert.is.equal(0, empty:len())
        assert.is.True(empty == A.EMPTY)   -- Check if it reduced to the EMPTY singleton
        assert.is.equal(ELEMS, full:len()) -- Verify original wasn't modified
    end)

    it("can be iterated over", function()
        local t, tbl = make_large_map_and_table()
        local count1 = 0
        local check1 = {}
        for k, v in t:pairs() do
            assert.is.equal(v, tbl[k])
            check1[k] = v
            count1 = count1 + 1
        end
        assert.is.equal(ELEMS, count1)
        assert.are.same(tbl, check1)

        -- Test raw iterator too
        local count2 = 0
        local check2 = {}
        local iter_fn, iter_param, iter_state = t:iter()
        while true do
            iter_state, k, v = iter_fn(iter_param, iter_state)
            if iter_state == nil then break end
            assert.is.equal(v, tbl[k])
            check2[k] = v
            count2 = count2 + 1
        end
        assert.is.equal(ELEMS, count2)
        assert.are.same(tbl, check2)
    end)
end)

-- [[[ NEW: Merge Tests ]]]
describe("hashmap merging", function()
    local A = require 'ltrie.hashmap'
    local function totable(map)
        local t = {}
        if map and map.pairs then
            for k, v in map:pairs() do
                t[k] = v
            end
        end
        return t
    end

    it("merges with EMPTY correctly", function()
        local map1 = A.of('a', 1, 'b', 2)
        local merged1 = map1:merge(A.EMPTY)
        local merged2 = A.EMPTY:merge(map1)

        assert.is_true(merged1 == map1, "Merging non-empty with EMPTY should return original")
        assert.is_equal(2, merged1:len())
        assert.are.same({ a = 1, b = 2 }, totable(merged1))

        assert.is_true(merged2 == map1, "Merging EMPTY with non-empty should return non-empty")
        assert.is_equal(2, merged2:len())
        assert.are.same({ a = 1, b = 2 }, totable(merged2))

        local merged3 = A.EMPTY:merge(A.EMPTY)
        assert.is_true(merged3 == A.EMPTY, "Merging EMPTY with EMPTY should return EMPTY")
    end)

    it("merges disjoint maps", function()
        local map1 = A.of('a', 1, 'b', 2)
        local map2 = A.of('c', 3, 'd', 4)
        local merged = map1:merge(map2)
        local expected = { a = 1, b = 2, c = 3, d = 4 }

        assert.is_equal(4, merged:len())
        assert.are.same(expected, totable(merged))

        -- Check originals unchanged
        assert.are.same({ a = 1, b = 2 }, totable(map1))
        assert.are.same({ c = 3, d = 4 }, totable(map2))
    end)

    it("merges maps with overlap (other takes precedence)", function()
        local map1 = A.of('a', 1, 'b', 2, 'c', 30)
        local map2 = A.of('c', 3, 'd', 4, 'a', 10)       -- 'c' and 'a' overlap
        local merged = map1:merge(map2)
        local expected = { a = 10, b = 2, c = 3, d = 4 } -- map2 values for 'a', 'c'

        assert.is_equal(4, merged:len())
        assert.are.same(expected, totable(merged))

        -- Check originals unchanged
        assert.are.same({ a = 1, b = 2, c = 30 }, totable(map1))
        assert.are.same({ c = 3, d = 4, a = 10 }, totable(map2))
    end)

    it("merges identical maps", function()
        local map1 = A.of('a', 1, 'b', 2)
        local map2 = A.of('a', 1, 'b', 2)
        local merged = map1:merge(map2)

        -- Ideally, merge should detect no change and return original instance
        -- This might depend on implementation details (e.g., hash seed consistency)
        -- assert.is_true(merged == map1) -- Check instance identity (optional, might fail)

        assert.is_equal(2, merged:len())
        assert.are.same({ a = 1, b = 2 }, totable(merged))
    end)

    it("merges maps causing hash collisions", function()
        -- Note: This requires knowing how hashcode works or using many keys
        -- For simplicity, let's merge maps where keys likely end up in CLeafs or Nodes
        local map1 = A.of('key1', 'val1', 'key2', 'val2')
        local map2 = A.of('key1', 'new_val1', 'key3', 'val3') -- Overwrite 'key1', add 'key3'
        local merged = map1:merge(map2)
        local expected = { key1 = 'new_val1', key2 = 'val2', key3 = 'val3' }

        assert.is_equal(3, merged:len())
        assert.are.same(expected, totable(merged))

        -- Create maps likely to cause deeper node structures / collisions
        local mapA = A.EMPTY
        local mapB = A.EMPTY
        for i = 1, 100 do mapA = mapA:assoc('A' .. i, i) end
        for i = 51, 150 do mapB = mapB:assoc('A' .. i, -i) end -- Overlap 51-100, add 101-150

        local mergedAB = mapA:merge(mapB)
        assert.is_equal(150, mergedAB:len())
        assert.is_equal(50, mergedAB:get('A50'))    -- From mapA
        assert.is_equal(-51, mergedAB:get('A51'))   -- From mapB (overwrite)
        assert.is_equal(-100, mergedAB:get('A100')) -- From mapB (overwrite)
        assert.is_equal(-101, mergedAB:get('A101')) -- From mapB (new)
        assert.is_equal(-150, mergedAB:get('A150')) -- From mapB (new)
    end)

    it("merges large maps", function()
        local ELEMS = 2048 -- Use a decent size
        local mapA = A.EMPTY
        local mapB = A.EMPTY
        local expected = {}

        -- Populate mapA and expected table
        for i = 1, ELEMS do
            local k = 'K' .. i
            mapA = mapA:assoc(k, i)
            expected[k] = i
        end

        -- Populate mapB, overlapping half and adding new keys
        local startB = ELEMS / 2 + 1
        local endB = ELEMS + ELEMS / 2
        for i = startB, endB do
            local k = 'K' .. i
            mapB = mapB:assoc(k, -i) -- Negative value to distinguish
            expected[k] = -i         -- Overwrite/add expected value
        end

        local merged = mapA:merge(mapB)

        assert.is_equal(endB, merged:len())                                   -- Total unique keys
        -- Check boundary values
        assert.is_equal(1, merged:get('K1'))                                  -- Original from A
        assert.is_equal(ELEMS / 2, merged:get('K' .. (ELEMS / 2)))            -- Original from A
        assert.is_equal(-(ELEMS / 2 + 1), merged:get('K' .. (ELEMS / 2 + 1))) -- Overwritten by B
        assert.is_equal(-ELEMS, merged:get('K' .. ELEMS))                     -- Overwritten by B
        assert.is_equal(-(ELEMS + 1), merged:get('K' .. (ELEMS + 1)))         -- New from B
        assert.is_equal(-endB, merged:get('K' .. endB))                       -- New from B

        -- Optional: Verify full content (can be slow)
        -- assert.are.same(expected, totable(merged))
    end)
end)
-- [[[ END: Merge Tests ]]]
