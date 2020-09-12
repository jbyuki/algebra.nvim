@*=
local store = {}
local a = setmetatable({}, {
	__newindex = function(tbl, key, val)
		for k,v in pairs(store) do
			if k[1] == key[1] and k[2] == key[2] then
				store[k] = val
				return
			end
		end
		store[key] = val
	end,
	__index = function(tbl, key)
		for k,v in pairs(store) do
			if k[1] == key[1] and k[2] == key[2] then
				return v
			end
		end
	end
})

a[{"name", 1}] = 2
a[{"name", 1}] = a[{"name", 1}] + 2
events = {}
table.insert(events, a[{"name", 1}])
