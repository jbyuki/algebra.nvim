@*=
@requres
@script_variables
@copy_files

@copy_files+=
local plugvim = io.open("../plugin/algebra.vim", "w")
for line in io.lines("tangle/algebra.vim") do
	plugvim:write(line .. '\n')
end
plugvim:close()

local pluglua = io.open("../lua/algebra.lua", "w")
for line in io.lines("tangle/algebra.lua") do
	pluglua:write(line .. '\n')
end
pluglua:close()
