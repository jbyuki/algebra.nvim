@*=
@requires
@declare_functions
@script_variables
@expressions
@tokens

@functions

@parse
@expand

return {
@export_symbols
}

@expand+=
local function expand()
	@get_current_string
	@parse_string
	-- @print_result
	@expand_expression
	@combine_symbols
end

@export_symbols+=
expand = expand,

@get_current_string+=
local line = vim.api.nvim_get_current_line()

@parse_string+=
local exp = parseAll(line)
if not exp then
	return
end

@declare_functions+=
local parseAll

@parse+=
function parseAll(str)
	@clear_tokens
	@tokenize_string
	@parse_tokens
	return exp
end

@clear_tokens+=
tokens = {}

@tokenize_string+=
local i = 1
while i <= string.len(str) do
	@get_character
	@skip_whitespace
	@tokenize_op
	@tokenize_par
	@tokenize_num
	@tokenize_symbol
	@handle_error_tokenize
end

@get_character+=
local c = string.sub(str, i, i)

@skip_whitespace+=
if string.match(c, "%s") then
	i = i+1 

@tokens+=
-- closure-based object
local function AddToken() local self = { kind = "add" }
	@add_token_methods
return self end
local function SubToken() local self = { kind = "sub" }
	@sub_token_methods
return self end
local function MulToken() local self = { kind = "mul" }
	@mul_token_methods
return self end
local function DivToken() local self = { kind = "div" }
	@div_token_methods
return self end

@script_variables+=
tokens = {}

@tokenize_op+=
elseif c == "+" then table.insert(tokens, AddToken()) i = i+1
elseif c == "-" then table.insert(tokens, SubToken()) i = i+1
elseif c == "*" then table.insert(tokens, MulToken()) i = i+1
elseif c == "/" then table.insert(tokens, DivToken()) i = i+1

@tokens+=
local function RParToken() local self = { kind = "rpar" }
	@rpar_token_methods
return self end
local function LParToken() local self = { kind = "lpar" }
	@lpar_token_methods
return self end

@tokenize_par+=
elseif c == "(" then table.insert(tokens, LParToken()) i = i+1
elseif c == ")" then table.insert(tokens, RParToken()) i = i+1

@tokens+=
local function NumToken(num) local self = { kind = "num", num = num }
	@num_token_methods
return self end

@tokenize_num+=
elseif string.match(c, "%d") then 
	local parsed = string.match(string.sub(str, i), "%d+%.?%d*")
	i = i+string.len(parsed)
	table.insert(tokens, NumToken(tonumber(parsed))) 

@script_variables+=
events = {}

@handle_error_tokenize+=
else
	table.insert(events, "Unexpected character insert " .. c)
	i = i+1
end

@tokens+=
local function SymToken(sym) local self = { kind = "sym", sym = sym }
	@sym_token_methods
return self end

@tokenize_symbol+=
elseif string.match(c, "%a") then
	@add_mul_token_if_num_just_before
	@get_all_char_sym
	@create_num_token_if_constant
	@otherwise_crete_sym_token

@add_mul_token_if_num_just_before+=
if #tokens > 0 and tokens[#tokens].kind == "num" then
	table.insert(tokens, MulToken())
end

@get_all_char_sym+=
local parsed = string.match(string.sub(str, i), "%a+")
i = i+string.len(parsed)

@declare_functions+=
local nocase

@functions+=
function nocase (s)
	s = string.gsub(s, "%a", function (c)
		if string.match(c, "[a-zA-Z]") then
			return string.format("[%s%s]", 
				string.lower(c),
				string.upper(c))
		else
			return c
		end
	end)
	return s
end

@create_num_token_if_constant+=
if string.match(parsed, "^" .. nocase("pi") .. "$") then
	table.insert(tokens, NumToken(3.14159265258979))
elseif string.match(parsed, "^" .. nocase("e") .. "$") then
	table.insert(tokens, NumToken(2.71828182845905))

@otherwise_crete_sym_token+=
else
	table.insert(tokens, SymToken(parsed))
end

@declare_functions+=
local nextToken

@script_variables+=
local token_index

@parse_tokens-=
token_index = 1

@functions+=
function nextToken()
	local token = tokens[token_index]
	token_index = token_index + 1
	return token
end

@declare_functions+=
local finish

@functions+=
function finish()
	return token_index > #tokens
end

@declare_functions+=
local getToken

@functions+=
function getToken()
	return tokens[token_index]
end

@parse_tokens+=
local exp = parse(0)

@declare_functions+=
local parse

@functions+=
function parse(p)
	local t = nextToken()
	if not t then
		return nil
	end

	if not t.prefix then
		print(t.kind)
	end
	local exp = t.prefix()

	while exp and not finish() and p <= getToken().priority() do
		t = nextToken()
		exp = t.infix(exp)
	end
	return exp
end

@add_token_methods+=
function self.prefix()
	return parse(self.priority())
end

@declare_functions+=
local AddExpression

@expressions+=
function AddExpression(left, right) 
	local self = { kind = "addexp", left = left, right = right }
	@add_exp_methods
return self end

@add_token_methods+=
function self.infix(left)
	local t = parse(self.priority())
	if not t then
		return nil
	end
	return AddExpression(left, t)
end
function self.priority() return 50 end

@declare_functions+=
local PrefixSubExpression

@expressions+=
function PrefixSubExpression(left) 
	local self = { kind = "presubexp", left = left }
	@presub_exp_methods
return self end

@sub_token_methods+=
function self.prefix()
	local t = parse(90)
	if not t then
		return nil
	end
	return PrefixSubExpression(t)
end

@declare_functions+=
local SubExpression

@expressions+=
function SubExpression(left, right)
	local self = { kind = "subexp", left = left, right = right }
	@sub_exp_methods
return self end

@sub_token_methods+=
function self.infix(left)
	local t = parse(self.priority()+1)
	if not t then
		return nil
	end
	-- return SubExpression(left, t)
	if t.kind == "numexp" then
		return AddExpression(left, NumExpression(-t.num))
	else
		return AddExpression(left, PrefixSubExpression(t))
	end
end
function self.priority() return 50 end

@declare_functions+=
local MulExpression

@expressions+=
function MulExpression(left, right)
	local self = { kind = "mulexp", left = left, right = right }
	@mul_exp_methods
return self end

@mul_token_methods+=
function self.infix(left)
	local t = parse(self.priority())
	if not t then
		return nil
	end
	return MulExpression(left, t)
end
function self.priority() return 60 end

@declare_functions+=
local DivExpression

@expressions+=
function DivExpression(left, right)
	local self = { kind = "divexp", left = left, right = right }
	@div_exp_methods
return self end

@div_token_methods+=
function self.infix(left)
	local t = parse(self.priority()+1)
	if not t then
		return nil
	end
	return DivExpression(left, t)
end
function self.priority() return 60 end

@lpar_token_methods+=
function self.prefix()
	local exp = parse(20)
	if not exp then
		return nil
	end
	@check_rpar
	return exp
end

@check_rpar+=
local rpar = nextToken()
if not rpar or rpar.kind ~= "rpar" then 
	table.insert(events, "Unmatched '('")
	return nil
end

@lpar_token_methods+=
function self.priority() return 100 end

@rpar_token_methods+=
function self.priority() return 10 end

@declare_functions+=
local NumExpression

@expressions+=
function NumExpression(num)
	local self = { kind = "numexp", num = num }
	@num_exp_methods
return self end

@num_token_methods+=
function self.prefix()
	return NumExpression(self.num)
end

@declare_functions+=
local SymExpression

@expressions+=
function SymExpression(sym)
	local self = { kind = "symexp", sym = sym }
	@sym_exp_methods
return self end

@sym_token_methods+=
function self.prefix()
	return SymExpression(self.sym)
end

@print_result+=
print(vim.inspect(exp))
print("result: " .. vim.inspect(exp.eval()))

@add_exp_methods+=
function self.eval() return self.left.eval() + self.right.eval() end
@sub_exp_methods+=
function self.eval() return self.left.eval() - self.right.eval() end
@mul_exp_methods+=
function self.eval() return self.left.eval() * self.right.eval() end
@div_exp_methods+=
function self.eval() return self.left.eval() / self.right.eval() end
@num_exp_methods+=
function self.eval() return self.num end
@sym_exp_methods+=
function self.eval() return 0 end
@presub_exp_methods+=
function self.eval() return -self.left.eval() end

@declare_functions+=
local FunExpression

@expressions+=
function FunExpression(name, left)
	local self = { kind = "funexp", name = name, left = left }
	@fun_exp_methods
return self end

@script_variables+=
local funs = {
	@list_supported_functions
}

@lpar_token_methods+=
function self.infix(left)
	local exp = parse(20)
	if not exp then
		return nil
	end
	@check_rpar
	local name = left.sym
	return FunExpression(name, exp)
end

@list_supported_functions+=
sin = math.sin,
cos = math.cos,
tan = math.tan,
sqrt = math.sqrt,
asin = math.asin,
acos = math.acos,
atan = math.atan,
ln = math.log,
log = math.log10,
exp = math.exp,
atan2 = math.atan2,
abs = math.abs,

@fun_exp_methods+=
function self.eval() return funs[self.name](self.left.eval()) end

@tokens+=
local function ExpToken() local self = { kind = "exp" }
	@exp_token_methods
return self end

@tokenize_op+=
elseif c == "^" then table.insert(tokens, ExpToken()) i = i+1

@declare_functions+=
local ExpExpression

@expressions+=
function ExpExpression(left, right)
	local self = { kind = "expexp", left = left, right = right }
	@exp_exp_methods
return self end

@exp_token_methods+=
function self.infix(left)
	local exp = parse(self.priority())
	if not exp then
		return nil
	end
	return ExpExpression(left, exp)
end
function self.priority() return 70 end

@exp_exp_methods+=
function self.eval() return math.pow(self.left.eval(), self.right.eval()) end

@mul_exp_methods+=
function self.expand()
	@get_upper_add_terms_while_expanding_them
	@cross_combine_terms
	return exp_add
end


@script_variables+=
local upper = {}

@mul_exp_methods-=
local collectUpperAddExpand

@mul_exp_methods+=
function collectUpperAddExpand(root, collect)
	if root.kind == "addexp" then
		collectUpperAddExpand(root.left, collect)
		collectUpperAddExpand(root.right, collect)
	else
		local expanded = root.expand()
		if root.kind == "mulexp" or root.kind == "expexp" then
			if expanded.kind == "addexp" then
				collectUpperAddExpand(expanded, collect)
			else
				table.insert(collect, expanded)
			end
		else
			table.insert(collect, expanded)
		end
	end
end

@get_upper_add_terms_while_expanding_them+=
local collectLeft = {}
local collectRight = {}
collectUpperAddExpand(self.left, collectLeft)
collectUpperAddExpand(self.right, collectRight)

@cross_combine_terms+=
local exp_add
for _,term1 in ipairs(collectLeft) do
	for _,term2 in ipairs(collectRight) do
		exp_mul = MulExpression(vim.deepcopy(term1), vim.deepcopy(term2))
		if exp_add then
			exp_add = AddExpression(exp_add, exp_mul)
		else
			exp_add = exp_mul
		end
	end
end

@add_exp_methods+=
function self.expand() 
	local t1 = self.left.expand()
	local t2 = self.right.expand()
	return AddExpression(t1, t2)
end
@sub_exp_methods+=
function self.expand() 
	local t1 = self.left.expand()
	local t2 = self.right.expand()
	return SubExpression(t1, t2)
end
@presub_exp_methods+=
function self.expand() 
	local t1 = self.left.expand()
	return PrefixSubExpression(t1)
end
@div_exp_methods+=
function self.expand() 
	local t1 = self.left.expand()
	local t2 = self.right.expand()
	return DivExpression(t1, t2)
end
@sym_exp_methods+=
function self.expand() 
	return SymExpression(self.sym) 
end
@num_exp_methods+=
function self.expand() 
	return NumExpression(self.num)
end
@fun_exp_methods+=
function self.expand() 
	local t1 = self.left.expand()
	return FunExpression(self.name, t1) 
end

@expand_expression+=
local expanded = exp.expand()
print("expanded : " .. expanded.toString())

@add_exp_methods+=
function self.toString() 
	return "(" .. self.left.toString() .. " + " .. self.right.toString() .. ")"
end
@sub_exp_methods+=
function self.toString() 
	return "(" .. self.left.toString() .. " - " .. self.right.toString() .. ")"
end
@presub_exp_methods+=
function self.toString() 
	return "(-" .. self.left.toString() .. ")"
end
@mul_exp_methods+=
function self.toString() 
	return "(" .. self.left.toString() .. " * " .. self.right.toString() .. ")"
end
@div_exp_methods+=
function self.toString() 
	return "(" .. self.left.toString() .. " / " .. self.right.toString() .. ")"
end
@exp_exp_methods+=
function self.toString() 
	return "(" .. self.left.toString() .. " ^ " .. self.right.toString() .. ")"
end
@sym_exp_methods+=
function self.toString() 
	return self.sym
end
@num_exp_methods+=
function self.toString() 
	return self.num
end
@fun_exp_methods+=
function self.toString() 
	return self.name .. "(" .. self.left.toString() .. ")"
end

@exp_exp_methods+=
function self.expand() 
	if self.right.kind == "numexp" and math.floor(self.right.num) == self.right.num and self.right.num > 1 then
		@expand_integer_exp_exp
	else
		return self 
	end
end

@expand_integer_exp_exp+=
local term1 = vim.deepcopy(self.left)
local term2
if self.right.num > 2 then
	term2 = ExpExpression(vim.deepcopy(self.left), NumExpression(self.right.num-1))
else 
	term2 = vim.deepcopy(self.left)
end
local exp = MulExpression(term1, term2)
return exp.expand()

@combine_symbols+=
local combined = expanded.combined()
print("simplifed " .. combined.toString())

@add_exp_methods-=
local collectUpperAddCombine

@add_exp_methods+=
function collectUpperAddCombine(root, constant, collect, collectPow, rest)
	if root.kind == "addexp" then
		constant = collectUpperAddCombine(root.left, constant, collect, collectPow, rest)
		constant = collectUpperAddCombine(root.right, constant, collect, collectPow, rest)
	else
		local combined = root.combined()
		if combined.kind == "presubexp" then
			@if_prefix_sub_add_but_negative_term
		else
			@otherwise_just_add_the_term
		end
	end
	return constant
end

@if_prefix_sub_add_but_negative_term+=
combined = combined.left
if combined.kind == "symexp" then
	if not collect[combined.sym] then
		collect[combined.sym] = 0
	end
	collect[combined.sym] = collect[combined.sym] - 1
elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	local powpair = {combined.left.sym, combined.right.num}
	if not collectPow[powpair] then
		collectPow[powpair] = 0
	end
	collectPow[powpair] = collectPow[powpair] - 1
elseif combined.kind == "numexp" then
	constant = constant - combined.num
else
	table.insert(rest, PrefixSubExpression(combined))
end

@otherwise_just_add_the_term+=
if combined.kind == "symexp" then
	if not collect[combined.sym] then
		collect[combined.sym] = 0
	end
	collect[combined.sym] = collect[combined.sym] + 1
elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	local powpair = {combined.left.sym, combined.right.num}
	if not collectPow[powpair] then
		collectPow[powpair] = 0
	end
	collectPow[powpair] = collectPow[powpair] + 1
elseif combined.kind == "numexp" then
	constant = constant + combined.num
else
	table.insert(rest, combined)
end

@add_exp_methods+=
function self.combined() 
	@remove_if_add_zero
	@combine_upper_add_terms

	-- print("add constant " .. constant)
	-- print("add collect " .. vim.inspect(collect))
	-- print("add collectPow " .. vim.inspect(storeCollectPow))
	-- print("add rest " .. vim.inspect(rest))

	local exp_add

	@combine_constant_if_there_is_one
	@combine_simple_terms_in_add
	@combine_pow_terms_in_add
	@combine_rest_terms_in_add

	exp_add = exp_add or NumExpression(0)
	return exp_add
end

@remove_if_add_zero+=
if self.left.kind == "numexp" and self.left.num == 0 then
	return self.right.combined()
end
if self.right.kind == "numexp" and self.right.num == 0 then
	return self.left.combined()
end

@combine_upper_add_terms+=
local constant = 0
local collect = {}
local collectPow = {}
@make_collect_pow_table_access
local rest = {}

constant = collectUpperAddCombine(self.left, constant, collect, collectPow, rest)
constant = collectUpperAddCombine(self.right, constant, collect, collectPow, rest)

@make_collect_pow_table_access+=
local storeCollectPow = {}
collectPow = setmetatable({}, {
	__newindex = function(tbl, key, val)
		for k,v in pairs(storeCollectPow) do
			if k[1] == key[1] and k[2] == key[2] then
				storeCollectPow[k] = val
				return
			end
		end
		storeCollectPow[key] = val
	end,
	__index = function(tbl, key)
		for k,v in pairs(storeCollectPow) do
			if k[1] == key[1] and k[2] == key[2] then
				return v
			end
		end
	end
})

@combine_constant_if_there_is_one+=
if constant ~= 0 then
	exp_add = NumExpression(constant)
end

@combine_simple_terms_in_add+=
for sym, num in pairs(collect) do
	if num ~= 0 then
		local exp_mul = SymExpression(sym)
		if math.abs(num) ~= 1 then
			exp_mul = MulExpression(NumExpression(math.abs(num)), exp_mul)
		end
		if num < 0 then
			exp_mul = PrefixSubExpression(exp_mul)
		end

		if not exp_add then
			exp_add = exp_mul
		else
			exp_add = AddExpression(exp_mul, exp_add)
		end
	end
end

@combine_pow_terms_in_add+=
for pow, num in pairs(storeCollectPow) do
	if num ~= 0 then
		local exp_mul
		local exp_exp = ExpExpression(SymExpression(pow[1]), NumExpression(pow[2]))
		if num == 1 then
			exp_mul = exp_exp
		else
			exp_mul = MulExpression(NumExpression(num), exp_exp)
		end

		if not exp_add then
			exp_add = exp_mul
		else
			exp_add = AddExpression(exp_mul, exp_add)
		end
	end
end

@combine_rest_terms_in_add+=
for _, term in ipairs(rest) do
	if not exp_add then
		exp_add = term
	else
		exp_add = AddExpression(exp_mul, term)
	end
end

@sub_exp_methods+=
function self.combined() 
	local t1 = self.left.combined()
	local t2 = self.right.combined()
	return SubExpression(t1, t2)
end
@presub_exp_methods+=
function self.combined() 
	local t1 = self.left.combined()
	return PrefixSubExpression(t1)
end
@mul_exp_methods-=
local collectUpperMul

@mul_exp_methods+=
function collectUpperMul(root, coeff, collect, rest)
	if root.kind == "mulexp" then
		coeff = collectUpperMul(root.left, coeff, collect, rest)
		coeff = collectUpperMul(root.right, coeff, collect, rest)
	else
		if root.kind == "presubexp" then
			@if_prefix_sub_add_negative_and_combine_left
		else
			@otherwise_combine_mul_directly
		end
	end
	return coeff
end

@if_prefix_sub_add_negative_and_combine_left+=
root = root.left
if root.kind == "symexp" then
	if not collect[root.sym] then
		collect[root.sym] = 0
	end
	collect[root.sym] = -(collect[root.sym] + 1)
elseif root.kind == "expexp" and root.left.kind == "symexp" and root.right.kind == "numexp" then
	if not collect[root.left.sym] then
		collect[root.left.sym] = 0
	end
	collect[root.left.sym] = -(collect[root.left.sym] + root.right.num)
elseif root.kind == "numexp" then
	coeff = coeff * -root.num
else
	table.insert(rest, PrefixSubExpression(root.combined()))
end

@otherwise_combine_mul_directly+=
if root.kind == "symexp" then
	if not collect[root.sym] then
		collect[root.sym] = 0
	end
	if collect[root.sym] < 0 then
		collect[root.sym] = collect[root.sym] - 1
	else 
		collect[root.sym] = collect[root.sym] + 1
	end
elseif root.kind == "expexp" and root.left.kind == "symexp" and root.right.kind == "numexp" then
	if not collect[root.left.sym] then
		collect[root.left.sym] = 0
	end
	if collect[root.left.sym] < 0 then
		collect[root.left.sym] = collect[root.left.sym] - root.right.num
	else
		collect[root.left.sym] = collect[root.left.sym] + root.right.num
	end
elseif root.kind == "numexp" then
	coeff = coeff * root.num
else
	table.insert(rest, root.combined())
end

@mul_exp_methods+=
function self.combined() 
	@remove_if_multiply_by_one
	@remove_if_multiply_by_minus_one
	@combine_terms_upper_mul

	local exp_mul
	@combine_coefficient
	@combine_unknown_power
	@combine_rest_terms

	exp_mul = exp_mul or NumExpression(0)
	return exp_mul
end

@remove_if_multiply_by_one+=
if self.left.kind == "numexp" and self.left.num == 1 then
	return self.right.combined()
end
if self.right.kind == "numexp" and self.right.num == 1 then
	return self.left.combined()
end

@remove_if_multiply_by_minus_one+=
if self.left.kind == "numexp" and self.left.num == -1 then
	return PrefixSubExpression(self.right.combined())
end
if self.right.kind == "numexp" and self.right.num == -1 then
	return PrefixSubExpression(self.left.combined())
end

@combine_terms_upper_mul+=
local collectAll = {}
local rest = {}
local coeff = 1
coeff = collectUpperMul(self.left, coeff, collectAll, rest)
coeff = collectUpperMul(self.right, coeff, collectAll, rest)

-- print("mul collectAll " .. vim.inspect(collectAll))
-- print("mul rest " .. vim.inspect(rest))
-- print("mul coeff " .. vim.inspect(coeff))

@declare_functions+=
local countMap

@declare_functions+=
function countMap(a)
	local c = 0
	for _,_ in pairs(a) do
		c = c+1
	end
	return c
end

@combine_coefficient+=
if coeff ~= 1 or (countMap(collectAll) == 0 and #rest == 0) then
	exp_mul = NumExpression(coeff)
end

@combine_unknown_power+=
for term, power in pairs(collectAll) do
	if power ~= 0 then
		local exp_pow = SymExpression(term)
		if math.abs(power) ~= 1 then
			exp_pow = ExpExpression(exp_pow, NumExpression(math.abs(power)))
		end

		if power < 0 then
			exp_pow = PrefixSubExpression(exp_pow)
		end

		if not exp_mul then
			exp_mul = exp_pow
		else
			exp_mul = MulExpression(exp_mul, exp_pow)
		end
	end
end

@combine_rest_terms+=
for _, term in ipairs(rest) do
	local exp_pow = term
	if not exp_mul then
		exp_mul = term
	else
		exp_mul = MulExpression(exp_mul, term)
	end
end

@div_exp_methods+=
function self.combined() 
	local t1 = self.left.combined()
	local t2 = self.right.combined()
	return DivExpression(t1, t2)
end
@exp_exp_methods+=
function self.combined() 
	local t1 = self.left.combined()
	local t2 = self.right.combined()
	return ExpExpression(t1, t2)
end
@sym_exp_methods+=
function self.combined() 
	return SymExpression(self.sym)
end
@num_exp_methods+=
function self.combined() 
	return NumExpression(self.num)
end
@fun_exp_methods+=
function self.combined() 
	local t1 = self.left.combined()
	return NumExpression(self.name, t1)
end
