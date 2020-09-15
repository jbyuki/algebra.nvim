@*=
@requires
@declare_functions
@script_variables
@expressions
@tokens

@functions

@parse
@expand
@assign
@simplify
@evalulate
@show_latex

return {
@export_symbols
}

@declare_functions+=
local expand

@expand+=
function expand(line)
	@parse_string
	@save_parsed_in_global
	@show_result
end


@parse_string+=
local exp = parseAll(line)
if not exp then
	return
end

@declare_functions+=
local parseAll

@parse+=
function parseAll(str)
	tokenize(str)
	@parse_tokens
	return exp
end

@declare_functions+=
local tokenize

@functions+=
function tokenize(str)
	@clear_tokens
	@tokenize_string
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
	@tokenize_bracket
	@tokenize_comma
	@tokenize_semicolon
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
local parsed = string.match(string.sub(str, i), "%w+")
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
function self.priority() return priority_list["add"] end

@script_variables+=
local priority_list = {
	@priority_list
}

@priority_list+=
["add"] = 50,

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
function self.priority() return priority_list["sub"] end

@priority_list+=
["sub"] = 50,

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
function self.priority() return priority_list["mul"] end

@priority_list+=
["mul"] = 60,

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
function self.priority() return priority_list["div"] end

@priority_list+=
["div"] = 70,

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
function self.priority() return priority_list["lpar"] end

@priority_list+=
["lpar"] = 100,

@rpar_token_methods+=
function self.priority() return priority_list["rpar"] end

@priority_list+=
["rpar"] = 10,

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

@add_exp_methods+=
function self.eval(env) return self.left.eval(env) + self.right.eval(env) end
@sub_exp_methods+=
function self.eval(env) return self.left.eval(env) - self.right.eval(env) end
@mul_exp_methods+=
function self.eval(env) return self.left.eval(env) * self.right.eval(env) end
@div_exp_methods+=
function self.eval(env) return self.left.eval(env) / self.right.eval(env) end
@num_exp_methods+=
function self.eval(env) return self.num end
@sym_exp_methods+=
function self.eval(env) 
	assert(env[self.sym], "symbol " .. self.sym .. " does not exist")
	return env[self.sym].val.eval(env)
end


@presub_exp_methods+=
function self.eval(env) return -self.left.eval(env) end

@declare_functions+=
local FunExpression

@expressions+=
function FunExpression(name, args)
	local self = { kind = "funexp", name = name, args = args }
	@fun_exp_methods
return self end

@script_variables+=
local funs = {
	@list_supported_functions
}

@lpar_token_methods+=
function self.infix(left)
	local args = {}
	while not finish() do
		local exp = parse(20)
		if not exp then
			return nil
		end
		table.insert(args, exp)
		local t = nextToken()
		@if_rpar_quit
		@if_comma_next_arg
	end
	local name = left.sym
	return FunExpression(name, args)
end

@if_rpar_quit+=
if t.kind == "rpar" then
	break
end

@if_comma_next_arg+=
assert(t.kind == "comma", "expected comma in function arg list")

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
function self.eval(env) 
	@evaluate_function_arguments
	if env[self.name] and env[self.name].kind == "fun" then
		@create_new_environment_with_arguments
		return env[self.name].val.eval(new_env)
	end
	return funs[self.name](unpack(fargs))
end

@evaluate_function_arguments+=
local fargs = {}
for _,arg in ipairs(self.args) do
	table.insert(fargs, arg.eval(env))
end

@create_new_environment_with_arguments+=
local new_env = setmetatable({}, { __index = env })
for i=1,#self.args do
	new_env[env[self.name].args[i]] = { 
		name = env[self.name].args[i], 
		val = NumExpression(fargs[i])
	}
end

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
function self.priority() return priority_list["exp"] end

@priority_list+=
["exp"] = 70,

@exp_exp_methods+=
function self.eval(env) return math.pow(self.left.eval(env), self.right.eval(env)) end

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
function self.arity()
	return #self.args
end

@fun_exp_methods+=
function self.expand() 
	@expand_function_args
	@apply_functions_for_expand
	return FunExpression(self.name, fargs) 
end

@expand_function_args+=
local fargs = {}
for _,arg in ipairs(self.args) do
	table.insert(fargs, arg.expand())
end


@declare_functions+=
local putParen

@functions+=
function putParen(exp, p)
	if exp.priority() < p then
		return "(" .. exp.toString() .. ")"
	else
		return exp.toString()
	end
end

@add_exp_methods+=
function self.toString() 
	if self.right.kind == "presubexp" then
		return putParen(self.left, self.priority()) .. "-" .. putParen(self.right.left, self.priority())
	elseif self.right.kind == "numexp" and self.right.num < 0 then
		return putParen(self.left, self.priority()) .. "-" .. putParen(NumExpression(math.abs(self.right.num)), self.priority())
	else
		return putParen(self.left, self.priority()) .. "+" .. putParen(self.right, self.priority())
	end
end
@sub_exp_methods+=
function self.toString() 
	return putParen(self.left, self.priority()) .. "-" .. putParen(self.right, self.priority())
end
@presub_exp_methods+=
function self.toString() 
	return "-" .. putParen(self.left, self.priority()) .. ""
end
@mul_exp_methods+=
function self.toString() 
	if self.left.kind == "numexp" and self.right.getLeft().kind ~= "numexp" then
		return putParen(self.left, self.priority()) .. putParen(self.right, self.priority())
	else 
		return putParen(self.left, self.priority()) .. "*" .. putParen(self.right, self.priority())
	end
end
@div_exp_methods+=
function self.toString() 
	return putParen(self.left, self.priority()) .. "/" .. putParen(self.right, self.priority())
end
@exp_exp_methods+=
function self.toString() 
	return putParen(self.left, self.priority()) .. "^" .. putParen(self.right, self.priority())
end
@sym_exp_methods+=
function self.toString() 
	return self.sym
end
@num_exp_methods+=
function self.toString() 
	return tostring(self.num)
end
@fun_exp_methods+=
function self.toString() 
	local fargs = {}
	for _,arg in ipairs(self.args) do
		table.insert(fargs, arg.toString())
	end
	return self.name .. "(" .. table.concat(fargs, ", ") .. ")"
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
local factor = -1
if combined.kind == "symexp" then
	@combine_add_sym_exp
elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	@combine_add_exp_exp
elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	local sym, num = combined.left.sym, combined.right.num
	@combine_add_mul_exp
elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
	local sym, num = combined.right.sym, combined.left.num
	@combine_add_mul_exp
elseif combined.kind == "mulexp" and combined.left.kind == "expexp" and combined.right.kind == "numexp" then
	if combined.left.left.kind == "symexp" and combined.left.right.kind == "numexp" then
		local sym, pow, num = combined.left.left.sym, combined.left.right.num, combined.right.num
		@combine_add_mul_exp_exp
	end
elseif combined.kind == "mulexp" and combined.right.kind == "expexp" and combined.left.kind == "numexp" then
	if combined.right.left.kind == "symexp" and combined.right.right.kind == "numexp" then
		local sym, pow, num = combined.right.left.sym, combined.right.right.num, combined.left.num
		@combine_add_mul_exp_exp
	end
elseif combined.kind == "numexp" then
	constant = constant - combined.num
else
	table.insert(rest, PrefixSubExpression(combined))
end

@combine_add_sym_exp+=
if not collect[combined.sym] then
	collect[combined.sym] = 0
end
collect[combined.sym] = collect[combined.sym] + factor*1

@combine_add_exp_exp+=
local powpair = {combined.left.sym, combined.right.num}
if not collectPow[powpair] then
	collectPow[powpair] = 0
end
collectPow[powpair] = collectPow[powpair] + factor*1

@combine_add_mul_exp+=
if not collect[sym] then
	collect[sym] = 0
end
collect[sym] = collect[sym] + factor*num

@combine_add_mul_exp_exp+=
local powpair = {sym, pow}
if not collectPow[powpair] then
	collectPow[powpair] = 0
end
collectPow[powpair] = collectPow[powpair] + factor*num

@otherwise_just_add_the_term+=
local factor = 1
if combined.kind == "symexp" then
	@combine_add_sym_exp
elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	@combine_add_exp_exp
elseif combined.kind == "numexp" then
	constant = constant + combined.num
elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	local sym, num = combined.left.sym, combined.right.num
	@combine_add_mul_exp
elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
	local sym, num = combined.right.sym, combined.left.num
	@combine_add_mul_exp
elseif combined.kind == "mulexp" and combined.left.kind == "expexp" and combined.right.kind == "numexp" then
	if combined.left.left.kind == "symexp" and combined.left.right.kind == "numexp" then
		local sym, pow, num = combined.left.left.sym, combined.left.right.num, combined.right.num
		@combine_add_mul_exp_exp
	end
elseif combined.kind == "mulexp" and combined.right.kind == "expexp" and combined.left.kind == "numexp" then
	if combined.right.left.kind == "symexp" and combined.right.right.kind == "numexp" then
		local sym, pow, num = combined.right.left.sym, combined.right.right.num, combined.left.num
		@combine_add_mul_exp_exp
	end
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
		elseif num == -1 then
			exp_mul = PrefixSubExpression(exp_exp)
		else
			exp_mul = MulExpression(NumExpression(num), exp_exp).combined()
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
		exp_add = AddExpression(exp_add, term)
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
	if t1.kind == "presubexp" then
		return t1.left.combined()
	elseif isZero(t1) then
		return t1.combined()
	end
	return PrefixSubExpression(t1)
end
@mul_exp_methods-=
local collectUpperMul

@mul_exp_methods+=
function collectUpperMul(root, coeff, collect, collectMat, rest)
	if root.kind == "mulexp" then
		coeff = collectUpperMul(root.left, coeff, collect, collectMat, rest)
		coeff = collectUpperMul(root.right, coeff, collect, collectMat, rest)
	else
		local combined = root.combined()
		if combined.kind == "presubexp" then
			coeff = coeff * -1
			combined = combined.left
		end
		@combine_mul_directly
	end
	return coeff
end

@declare_functions+=
local copysign

@functions+=
function copysign(mag, sign)
	if sign < 0 then
		return -math.abs(mag)
	else
		return math.abs(mag)
	end
end

@combine_mul_sym_exp+=
if not collect[combined.sym] then
	collect[combined.sym] = 0
end
collect[combined.sym] = copysign(math.abs(collect[combined.sym])+1, collect[combined.sym])

@combine_mul_exp_exp+=
if not collect[combined.left.sym] then
	collect[combined.left.sym] = 0
end
collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) + combined.right.num, collect[combined.left.sym])

@combine_mul_directly+=
if combined.kind == "symexp" then
	@combine_mul_sym_exp
elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
	local sym, num = combined.left.sym, combined.right.num
	@combine_mul_exp_exp
elseif combined.kind == "numexp" then
	coeff = coeff * combined.num
@add_mat_mul_term
else
	table.insert(rest, combined)
end

@add_mat_mul_term+=
elseif combined.kind == "matexp" then
	table.insert(collectMat, combined)

@combine_mat_if_only_one+=
if #collectMat > 0 then
	local exp_mat
	@multiply_the_matrices_together
	if exp_mul then
		@multiply_coefficient_to_every_mat_cell
	else
		exp_mul = exp_mat
	end
end

@multiply_the_matrices_together+=
exp_mat = collectMat[1]
for i=2,#collectMat do
	exp_mat = MulExpression(exp_mat, collectMat[i]).combinedMatrix()
end

@multiply_coefficient_to_every_mat_cell+=
local rows = {}
for i=1,exp_mat.m do
	local new_row = {}
	for j=1,exp_mat.n do
		table.insert(new_row, MulExpression(exp_mul, exp_mat.rows[i][j]).expand().combined())
	end
	table.insert(rows, new_row)
end
exp_mul = MatrixExpression(rows, exp_mat.m, exp_mat.n)

@mul_exp_methods+=
function self.combined() 
	@remove_if_multiply_by_one
	@remove_if_multiply_by_minus_one
	@combine_terms_upper_mul

	-- print("mul collectAll " .. vim.inspect(collectAll))
	-- print("mul rest " .. vim.inspect(rest))
	-- print("mul coeff " .. vim.inspect(coeff))

	local exp_mul
	@combine_unknown_power
	@combine_rest_terms
	@combine_coefficient
	@combine_mat_if_only_one

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
	return (PrefixSubExpression(self.right.combined())).combined()
end
if self.right.kind == "numexp" and self.right.num == -1 then
	return (PrefixSubExpression(self.left.combined())).combined()
end

@combine_terms_upper_mul+=
local collectAll = {}
local rest = {}
local coeff = 1
local collectMat = {}
coeff = collectUpperMul(self.left, coeff, collectAll, collectMat, rest)
coeff = collectUpperMul(self.right, coeff, collectAll, collectMat, rest)


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
if math.abs(coeff) ~= 1 or (countMap(collectAll) == 0 and #rest == 0) then
	if not exp_mul then
		exp_mul = NumExpression(coeff)
	else
		exp_mul = MulExpression(NumExpression(coeff), exp_mul)
	end
elseif coeff == -1 then
	exp_mul = PrefixSubExpression(exp_mul)
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
			exp_mul = MulExpression(exp_mul, exp_pow.combined())
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
	if isOne(t2) then
		return t1
	else
		return ExpExpression(t1, t2)
	end
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
	local fargs = {}
	for _,arg in ipairs(self.args) do
		table.insert(fargs, arg.combined())
	end
	return FunExpression(self.name, fargs)
end

@declare_functions+=
local isZero

@functions+=
function isZero(exp)
	if exp.kind == "numexp" and exp.num == 0 then
		return true
	@matrix_zero
	end
	return false
end

@add_exp_methods+=
function self.derive(sym) 
	local t1 = self.left.derive(sym)
	local t2 = self.right.derive(sym)

	if isZero(t1) then return t2 end
	if isZero(t2) then return t1 end

	return AddExpression(t1, t2)
end
@sub_exp_methods+=
function self.derive(sym) 
	local t1 = self.left.derive(sym)
	local t2 = self.right.derive(sym)

	if isZero(t1) then return PrefixSubExpression(t2) end
	if isZero(t2) then return t1 end

	return SubExpression(t1, t2)
end
@presub_exp_methods+=
function self.derive(sym) 
	local t1 = self.left.derive(sym)
	if isZero(t1) then return t1 end
	return PrefixSubExpression(t1)
end
@mul_exp_methods+=
function self.derive(sym) 
	-- u'v + uv'
	local t1 = self.left.derive(sym)
	local t2 = self.right.derive(sym)

	local p1 = MulExpression(t1, vim.deepcopy(self.right))
	local p2 = MulExpression(vim.deepcopy(self.left), t2)

	if isZero(t1) then return p2 end
	if isZero(t2) then return p1 end

	return AddExpression(p1, p2)
end
@div_exp_methods+=
function self.derive(sym) 
	-- (u'v - uv')/v^2
	local t1 = self.left.derive(sym)
	local t2 = self.right.derive(sym)

	local p1 = MulExpression(t1, vim.deepcopy(self.right))
	local p2 = MulExpression(vim.deepcopy(self.left), t2)
	local den = MulExpression(vim.deepcopy(self.right), vim.deepcopy(self.right))

	if isZero(t1) then
		local d = DivExpression(p2, den)
		return PrefixSubExpression(d)
	end

	if isZero(t2) then
		return DivExpression(t1, vim.deepcopy(self.right))
	end

	local num = SubExpression(p1, p2)
	return DivExpression(num, den)
end
@exp_exp_methods+=
function self.derive(sym) 
	-- just support constant number exponents
	if self.right.kind == "numexp" then
		local exp = self.right.num
		if exp == 1 then
			return self.left.derive(sym)
		end

		local x = ExpExpression(vim.deepcopy(self.left), NumExpression(exp-1))
		local l = MulExpression(vim.deepcopy(self.right), x)

		@composition_rule
		return p
	end
end

@declare_functions+=
local isOne

@functions+=
function isOne(exp)
	return exp.kind == "numexp" and exp.num == 1
end

@composition_rule+=
local t1 = self.left.derive(sym)
local p = MulExpression(l, t1)
if isZero(t1) then
	return t1
elseif isOne(t1) then
	p = l
end
@sym_exp_methods+=
function self.derive(sym) 
	if self.sym == sym then 
		return NumExpression(1) 
	else return NumExpression(0) end
end
@num_exp_methods+=
function self.derive(sym) 
	return NumExpression(0)
end
@fun_exp_methods+=
function self.derive(sym) 
	@derive_functions
	else 
		table.insert(events, "Unknown function " .. self.name)
	end
end

@derive_functions+=
if self.name == "" then
elseif self.name == "cos" then
	-- -sin(u)*u'
	local l = FunExpression("sin", vim.deepcopy(self.args[1]))
	@composition_rule
	return PrefixSubExpression(p)
elseif self.name == "sin" then
	-- cos(u)*u'
	local l = FunExpression("cos", vim.deepcopy(self.args[1]))
	@composition_rule
	return p
elseif self.name == "sqrt" then
	-- u'/(2*sqrt(u))
	local t1 = self.args[1].derive(sym)
	if isZero(t1) then
		return t1
	end

	local p = MulExpression(NumExpression(2), vim.deepcopy(self))
	local d = DivExpression(t1, p)
	return d


@add_exp_methods+=
function self.priority() 
	return priority_list["add"]
end
@sub_exp_methods+=
function self.priority() 
	return priority_list["sub"]
end
@presub_exp_methods+=
function self.priority() 
	return priority_list["presub"]
end
@priority_list+=
["presub"] = 90,
@mul_exp_methods+=
function self.priority() 
	return priority_list["mul"]
end
@div_exp_methods+=
function self.priority() 
	return priority_list["div"]
end
@exp_exp_methods+=
function self.priority() 
	return priority_list["exp"]
end
@priority_list+=
["exp"] = 90,
@sym_exp_methods+=
function self.priority() 
	return priority_list["sym"]
end
@priority_list+=
["sym"] = 110,
@num_exp_methods+=
function self.priority() 
	return priority_list["num"]
end
@priority_list+=
["num"] = 110,
@fun_exp_methods+=
function self.priority() 
	return priority_list["fun"]
end
@priority_list+=
["fun"] = 100,

@declare_functions+=
local putParenLatex

@functions+=
function putParenLatex(exp, p)
	if exp.priority() < p then
		return "(" .. exp.toLatex() .. ")"
	else
		return exp.toLatex()
	end
end

@add_exp_methods+=
function self.toLatex() 
	return putParen(self.left, self.priority()) .. ((self.right.kind == "presubexp" and ("-" .. putParen(self.right.left, self.priority()))) or ("+" .. putParen(self.right, self.priority())))
end
@sub_exp_methods+=
function self.toLatex() 
	return putParenLatex(self.left, self.priority()) .. "-" .. putParenLatex(self.right, self.priority())
end
@presub_exp_methods+=
function self.toLatex() 
	return "-" .. putParenLatex(self.left, self.priority()) .. ""
end
@mul_exp_methods+=
function self.toLatex() 
	if self.left.kind == "numexp" and self.right.kind ~= "numexp" then
		return putParenLatex(self.left, self.priority()) .. putParenLatex(self.right, self.priority())
	else
		return putParenLatex(self.left, self.priority()) .. " \\cdot " .. putParenLatex(self.right, self.priority())
	end
end
@div_exp_methods+=
function self.toLatex() 
	return "\\frac{" .. self.left.toLatex() .. "}{" .. self.right.toLatex() .. "}"
end
@exp_exp_methods+=
function self.toLatex() 
	return putParenLatex(self.left, self.priority()) .. "^" .. putParenLatex(self.right, self.priority())
end
@sym_exp_methods+=
function self.toLatex() 
	return self.sym
end
@num_exp_methods+=
function self.toLatex() 
	return self.num
end
@fun_exp_methods+=
function self.toLatex() 
	if funs[self.name] then
		return "\\" .. self.name .. "{" .. self.args[1].toLatex() .. "}"
	else
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.toLatex())
		end
		return self.name .. "(" .. table.concat(fargs, ", ") .. ")"
	end
end


@tokenize_bracket+=
elseif c == "[" then table.insert(tokens, LBraToken()) i = i+1
elseif c == "]" then table.insert(tokens, RBraToken()) i = i+1
@tokenize_comma+=
elseif c == "," then table.insert(tokens, CommaToken()) i = i+1
@tokenize_semicolon+=
elseif c == ";" then table.insert(tokens, SemiToken()) i = i+1

@tokens+=
-- right bracket
local function LBraToken() local self = { kind = "lbra" }
	@lbra_token_methods
return self end
-- left bracket
local function RBraToken() local self = { kind = "rbra" }
	@rbra_token_methods
return self end
-- comma
local function CommaToken() local self = { kind = "comma" }
	@comma_token_methods
return self end
-- semi-colon
local function SemiToken() local self = { kind = "semi" }
	@semi_token_methods
return self end

@lbra_token_methods+=
function self.prefix()
	local i, j = 1, 1
	rows = {}
	rows[1] = {}
	while true do
		local exp = parse(10)
		if not exp then
			return nil
		end

		rows[i][j] = exp

		local t = nextToken()
		@if_rbra_quit
		@if_comma_next_col
		@if_semi_next_row
	end
	@verify_all_lines_have_same_length
	@make_matrix_expression
	return exp
end

@rbra_token_methods+=
function self.priority() return priority_list["rbra"] end
@priority_list+=
["rbra"] = 5,
@comma_token_methods+=
function self.priority() return priority_list["comma"] end
@priority_list+=
["comma"] = 5,
@semi_token_methods+=
function self.priority() return priority_list["semi"] end
@priority_list+=
["semi"] = 5,

@if_rbra_quit+=
if t.kind == "rbra" then
	break
end

@if_comma_next_col+=
if t.kind == "comma" then
	j = j+1
end

@if_semi_next_row+=
if t.kind == "semi" then
	rows[#rows+1] = {}
	i = i+1
	j = 1
end

@verify_all_lines_have_same_length+=
local curlen
for _,row in ipairs(rows) do
	if not curlen then
		curlen = #row
	end

	if #row ~= curlen then
		table.insert(events, "matrix dimension incorrect")
	end
end

@expressions+=
function MatrixExpression(rows, m, n)
	local self = { kind = "matexp", rows = rows, m = m, n = n }
	@mat_exp_methods
return self end

@make_matrix_expression+=
local exp = MatrixExpression(rows, #rows, curlen)

@mat_exp_methods+=
function self.toString()
	local rowsString = {}
	for _,row in ipairs(self.rows) do
		local cells = {}
		for _,cell in ipairs(row) do
			table.insert(cells, cell.toString())
		end
		local cellsString = table.concat(cells, ",")
		table.insert(rowsString, cellsString)
	end
	return "[" .. table.concat(rowsString, ";") .. "]"
end

@mat_exp_methods+=
function self.expand()
	local new_rows = {}
	for _,row in ipairs(self.rows) do
		local new_cells = {}
		for _,cell in ipairs(row) do
			table.insert(new_cells, cell.expand())
		end
		table.insert(new_rows, new_cells)
	end
	return MatrixExpression(new_rows, self.m, self.n)
end
function self.combined()
	local new_rows = {}
	for _,row in ipairs(self.rows) do
		local new_cells = {}
		for _,cell in ipairs(row) do
			table.insert(new_cells, cell.combined())
		end
		table.insert(new_rows, new_cells)
	end
	return MatrixExpression(new_rows, self.m, self.n)
end
function self.derive(sym)
	local new_rows = {}
	for _,row in ipairs(self.rows) do
		local new_cells = {}
		for _,cell in ipairs(row) do
			table.insert(new_cells, cell.derive(sym))
		end
		table.insert(new_rows, new_cells)
	end
	return MatrixExpression(new_rows, self.m, self.n)
end
function self.toLatex()
	local s = "\\begin{pmatrix}\n"
	for _,row in ipairs(self.rows) do
		local cells = {}
		for _,cell in ipairs(row) do
			table.insert(cells, cell.toLatex())
		end
		s = s .. table.concat(cells, " & ") .. "\\\\ \n"
	end
	s = s .. "\\end{pmatrix}"
	return s
end

@mat_exp_methods+=
function self.priority() 
	return priority_list["mat"]
end
@priority_list+=
["mat"] = 110,

@add_exp_methods+=
function self.combinedMatrix()
	local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
	local m2 = (self.right.combinedMatrix and self.right.combinedMatrix()) or self.right
	if m1.kind == "matexp" and m2.kind == "matexp" then
		@check_that_matrices_are_same_dimensions
		@add_matrices_together
		return MatrixExpression(rows)
	else
		return AddExpression(m1, m2)
	end
end

@check_that_matrices_are_same_dimensions+=
if m1.m ~= m2.m or m1.n ~= m2.n then
	table.insert(events, "add matrix dimensions mismatch")
	return
end

@add_matrices_together+=
rows = {}
for i=1,m1.m do
	result_row = {}
	for j=1,m1.n do
		table.insert(result_row, AddExpression(m1.rows[i][j], m2.rows[i][j]))
	end
	table.insert(rows, result_row)
end

@sub_exp_methods+=
function self.combinedMatrix()
	local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
	local m2 = (self.right.combinedMatrix and self.right.combinedMatrix()) or self.right
	if m1.kind == "matexp" and m2.kind == "matexp" then
		@check_that_matrices_are_same_dimensions
		@sub_matrices_together
		return MatrixExpression(rows)
	else
		return SubExpression(m1, m2)
	end
end

@sub_matrices_together+=
rows = {}
for i=1,m1.m do
	result_row = {}
	for j=1,m1.n do
		table.insert(result_row, SubExpression(m1.rows[i][j], m2.rows[i][j]))
	end
	table.insert(rows, result_row)
end

@presub_exp_methods+=
function self.combinedMatrix()
	local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
	if m1.kind == "matexp" then
		@presub_matrix
		return MatrixExpression(rows)
	else
		return PrefixSubExpression(m1)
	end
end

@presub_matrix+=
rows = {}
for i=1,m1.m do
	result_row = {}
	for j=1,m1.n do
		table.insert(result_row, PrefixSubExpression(m1.rows[i][j]))
	end
	table.insert(rows, result_row)
end

@mul_exp_methods+=
function self.combinedMatrix()
	local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
	local m2 = (self.right.combinedMatrix and self.right.combinedMatrix()) or self.right
	@check_that_matrices_are_correct_for_multiplication
	if m1.kind == "matexp" and m2.kind == "matexp" then
		@multiply_matrices_together
		return MatrixExpression(rows, #rows, #rows[1])
	else
		return MulExpression(m1, m2)
	end
end

@check_that_matrices_are_correct_for_multiplication+=
if m1.m ~= m2.n or m1.n ~= m2.m then
	table.insert(events, "Matrix mul dimensions mismatch " .. m1.m .. "x" .. m1.n .. " times " .. m2.m .. "x" .. m2.n)
	return
end

@multiply_matrices_together+=
rows = {}
for i=1,m2.n do
	for j=1,m1.m do
		local cell
		@compute_matrix_cell
		@put_result_in_cell
	end
end

@compute_matrix_cell+=
for k=1,m1.n do
	local exp = MulExpression(m1.rows[j][k], m2.rows[k][i])
	cell = (not cell and exp) or AddExpression(cell, exp)
end

@put_result_in_cell+=
if not rows[j] then
	rows[j] = {}
end
rows[j][i] = cell

@matrix_zero+=
elseif exp.kind == "matexp" then
	for i=1,exp.m do
		for j=1,exp.n do
			if not isZero(exp.rows[i][j]) then
				return false
			end
		end
	end
	return true

@add_exp_methods+=
function self.getLeft() 
	return self.left.getLeft()
end
@sub_exp_methods+=
function self.getLeft() 
	return self.left.getLeft()
end
@presub_exp_methods+=
function self.getLeft() 
	return self
end
@mul_exp_methods+=
function self.getLeft() 
	return self.left.getLeft()
end
@div_exp_methods+=
function self.getLeft() 
	return self.left.getLeft()
end
@exp_exp_methods+=
function self.getLeft() 
	return self.left.getLeft()
end
@sym_exp_methods+=
function self.getLeft() 
	return self
end
@num_exp_methods+=
function self.getLeft() 
	return self
end
@fun_exp_methods+=
function self.getLeft() 
	return self
end
@mat_exp_methods+=
function self.getLeft() 
	return self
end

@declare_functions+=
local assign

@assign+=
function assign(line)
	@look_for_assign_symbol
	@get_left_from_assign_symbol_and_parse
	local symEntry
	@if_paren_set_new_function_variable
	@otherwise_just_regular_variable
	@get_right_side_of_variable_and_parse
	@compute_exp_right_side_assignment
	@assign_exp_in_symbol_table
end

@look_for_assign_symbol+=
local i1, i2 = string.find(line, ":=")
assert(i1, "expected :=")

@get_left_from_assign_symbol_and_parse+=
local left = string.sub(line, 1, i1-1)
tokenize(left)

@if_paren_set_new_function_variable+=
if string.find(left, "%(") then
	@parse_function_name_and_arguments

@parse_function_name_and_arguments+=
assert(#tokens > 2, "function symbol expected tokens")
assert(tokens[1].kind == "sym", "function argument expected symbol")
local name = tokens[1].sym
local args = {}
assert(tokens[2].kind == "lpar", "function symbol expected left parenthesis")
i = 2
while tokens[i] and tokens[i].kind ~= "rpar" do
	i = i + 1
	assert(tokens[i] and tokens[i].kind == "sym", "function argument expected symbol")
	table.insert(args, tokens[i].sym)
	i = i + 1
end

symEntry = {
	name = name,
	kind = "fun",
	args = args
}

@otherwise_just_regular_variable+=
else
	assert(#tokens == 1, "variable name expected token")
	assert(tokens[1].kind == "sym", "variable name expected symbol")
	local name = tokens[1].sym

	symEntry = {
		name = name,
		kind = "var",
	}
end

@get_right_side_of_variable_and_parse+=
local right = string.sub(line, i2+1)
local exp = parseAll(right)
if not exp then
	return
end

@script_variables+=
symTable = {}

@assign_exp_in_symbol_table+=
symEntry.val = exp
symTable[symEntry.name] = symEntry

@functions+=
local function printSymTable()
	print("Symbol table:")
	for name, sym in pairs(symTable) do
		print(name .. " := " .. sym.val.toString())
	end
end

@export_symbols+=
printSymTable = printSymTable,

@add_exp_methods+=
function self.substitute() 
	local t1 = self.left.substitute()
	local t2 = self.right.substitute()
	return AddExpression(t1, t2)
end
@sub_exp_methods+=
function self.substitute() 
	local t1 = self.left.substitute()
	local t2 = self.right.substitute()
	return SubExpression(t1, t2)
end
@presub_exp_methods+=
function self.substitute() 
	local t1 = self.left.substitute()
	return PrefixSubExpression(t1, t2)
end
@mul_exp_methods+=
function self.substitute() 
	local t1 = self.left.substitute()
	local t2 = self.right.substitute()
	return MulExpression(t1, t2)
end
@div_exp_methods+=
function self.substitute() 
	local t1 = self.left.substitute()
	local t2 = self.right.substitute()
	return DivExpression(t1, t2)
end
@exp_exp_methods+=
function self.substitute() 
	local t1 = self.left.substitute()
	local t2 = self.right.substitute()
	return ExpExpression(t1, t2)
end
@sym_exp_methods+=
function self.substitute() 
	if symTable[self.sym] and symTable[self.sym].kind == "var" and symTable[self.sym].val.kind ~= "numexp" then
		return symTable[self.sym].val.substitute()
	end
	return self
end
@num_exp_methods+=
function self.substitute() 
	return NumExpression(self.num)
end
@fun_exp_methods+=
function self.substitute() 
	local fargs = {}
	for _,arg in ipairs(self.args) do
		table.insert(fargs, arg.substitute())
	end
	return FunExpression(self.name, fargs)
end
@mat_exp_methods+=
function self.substitute() 
	local rows = {}
	for i=1,self.m do
		row = {}
		for j=1,self.n do
			table.insert(row, self.rows[i][j].substitute())
		end
		table.insert(rows, row)
	end
	return MatrixExpression(rows, self.m, self.n)
end

@apply_functions_for_expand+=
if self.name == "grad" and #fargs == 1 and fargs[1].kind == "symexp" then
	local t1 = fargs[1]
	if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
		local symEntry = symTable[t1.sym]
		local args = symEntry.args
		assert(symEntry.val.kind ~= "matexp", "grad() expected matrix")
		@apply_grad
		@make_function_for_matrix
		return SymExpression(newSymEntry.name)
	end
end

@apply_grad+=
local rows = {}
for _, arg in ipairs(args) do
	table.insert(rows, { symEntry.val.derive(arg) })
end

@script_variables+=
local answerIndex = 1

@make_function_for_matrix+=
local newSymEntry = {
	name = answerIndex,
	kind = "fun",
	args = args,
	val = MatrixExpression(rows, #args, 1).expand().combined()
}
answerIndex = answerIndex + 1
symTable[newSymEntry.name] = newSymEntry

@apply_functions_for_expand+=
if self.name == "div" and #fargs == 1 and fargs[1].kind == "symexp" then
	local t1 = fargs[1]
	if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
		local symEntry = symTable[t1.sym]
		local args = symEntry.args
		local exp_add
		assert(symEntry.val.kind ~= "matexp", "div() expected matrix")
		@apply_div
		@make_function_for_exp_add
		return SymExpression(newSymEntry.name)
	end
end

@apply_div+=
for _, arg in ipairs(args) do
	local t = symEntry.val.derive(arg)
	exp_add = (exp_add and AddExpression(exp_add, t)) or t
end

@make_function_for_exp_add+=
local newSymEntry = {
	name = answerIndex,
	kind = "fun",
	args = args,
	val = exp_add.expand().combined()
}
answerIndex = answerIndex + 1
symTable[newSymEntry.name] = newSymEntry

@apply_functions_for_expand+=
if self.name == "rot" and #fargs == 1 and fargs[1].kind == "symexp" then
	local t1 = fargs[1]
	local arg
	if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
		local symEntry = symTable[t1.sym]
		local args = symEntry.args

		assert(symEntry.val.kind == "matexp", "rot() expected matrix")
		assert(symEntry.val.m == 3 and symEntry.val.n == 1, "rot() expected matrix dimension 3x1, found: " .. symEntry.val.m .. "x" .. symEntry.val.n)

		local rows = {}
		@apply_rot
		@make_function_for_matrix
		return SymExpression(newSymEntry.name)
	end
end

@apply_rot+=
rows = {}
local mat = symEntry.val
rows[1] = { AddExpression(mat.rows[3][1].derive(args[2]), PrefixSubExpression(mat.rows[2][1].derive(args[3]))) }
rows[2] = { AddExpression(mat.rows[1][1].derive(args[3]), PrefixSubExpression(mat.rows[3][1].derive(args[1]))) }
rows[3] = { AddExpression(mat.rows[2][1].derive(args[1]), PrefixSubExpression(mat.rows[1][1].derive(args[2]))) }

@apply_functions_for_expand+=
if self.name == "laplace" and #fargs == 1 and fargs[1].kind == "symexp" then
	local t1 = fargs[1]
	if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
		local symEntry = symTable[t1.sym]
		local args = symEntry.args
		local exp_add
		assert(symEntry.val.kind ~= "matexp", "laplace() expected matrix")
		@apply_laplace
		@make_function_for_exp_add
		return SymExpression(newSymEntry.name)
	end
end


@apply_laplace+=
for _, arg in ipairs(args) do
	local t = symEntry.val.derive(arg).derive(arg)
	exp_add = (exp_add and AddExpression(exp_add, t)) or t
end

@div_exp_methods+=
function self.combinedMatrix() 
	local t1 = self.left.combinedMatrix()
	local t2 = self.right.combinedMatrix()
	return DivExpression(t1, t2)
end

@declare_functions+=
local isInteger

@functions+=
function isInteger(x)
	return math.floor(x) == x
end

@exp_exp_methods+=
function self.combinedMatrix() 
	local t1 = self.left.combinedMatrix()
	local t2 = self.right.combinedMatrix()
	if t2.kind == "numexp" and isInteger(t2.num) and  t2.num > 1 then
		@do_mat_exp
	elseif t2.kind == "numexp" and t2.num == 1 then
		return t1
	end
	return ExpExpression(t1, t2)
end

@do_mat_exp+=
local tomult = MulExpression(t1, ExpExpression(vim.deepcopy(t1), NumExpression(t2.num-1)))
return tomult.combinedMatrix()

@sym_exp_methods+=
function self.combinedMatrix() 
	return SymExpression(self.sym)
end
@num_exp_methods+=
function self.combinedMatrix() 
	return NumExpression(self.num)
end
@fun_exp_methods+=
function self.combinedMatrix() 
	local fargs = {}
	for _,arg in ipairs(self.args) do
		table.insert(fargs, arg.combinedMatrix())
	end
	return FunExpression(self.name, fargs)
end
@mat_exp_methods+=
function self.combinedMatrix() 
	local rows = {}
	for i=1,self.m do
		row = {}
		for j=1,self.n do
			table.insert(row, self.rows[i][j].combinedMatrix())
		end
		table.insert(rows, row)
	end
	return MatrixExpression(rows, self.m, self.n)
end

@script_variables+=
answer = nil

@save_parsed_in_global+=
answer = exp
local symEntry = {
	name = "answer",
	kind = "var",
	val = exp
}
symTable["answer"] = symEntry

@show_result+=
local res = exp.substitute().expand().combined()
local line = res.toString()
vim.api.nvim_buf_set_lines(0, -1, -1, true, { line })

@compute_exp_right_side_assignment+=
exp = exp.substitute().expand().combined()
print(symEntry.name .. " := " .. exp.toString())

@simplify+=
function simplify()
	@get_current_string
	@if_has_assignement_sign_do_assignement
	@otherwise_just_expand_the_expression
end

@export_symbols+=
simplify = simplify,

@get_current_string+=
local line = vim.api.nvim_get_current_line()

@if_has_assignement_sign_do_assignement+=
if string.match(line, ":=") then
	assign(line)

@otherwise_just_expand_the_expression+=
else
	expand(line)
end

@simplify+=
function evaluate()
	@get_current_string
	@parse_string
	@save_parsed_in_global
	@evaluate_expression_and_output
end

@export_symbols+=
evaluate = evaluate,

@evaluate_expression_and_output+=
local res = tostring(exp.eval(symTable))
vim.api.nvim_buf_set_lines(0, -1, -1, true, { res })

@list_supported_functions+=
cosd = function(x) return math.cos(x*(math.pi/180.0)) end,
sind = function(x) return math.sin(x*(math.pi/180.0)) end,
tand = function(x) return math.tan(x*(math.pi/180.0)) end,
acosd = function(x) return math.acos(x)*(180.0/math.pi) end,
asind = function(x) return math.asin(x)*(180.0/math.pi) end,
atand = function(x) return math.atan(x)*(180.0/math.pi) end,

@show_latex+=
local function show_latex()
	@get_current_string
	@parse_string
	@generate_latex
end

@export_symbols+=
show_latex = show_latex,

@generate_latex+=
f = io.open("out.tex", "w")
f:write("\\documentclass[a4paper]{slides}\n")
f:write("\\begin{document}\n")
f:write("$" .. exp.toLatex() .. "$\n")
f:write("\\end{document}\n")
f:close()
vim.api.nvim_command("!pandoc out.tex -o out.pdf")
vim.api.nvim_command("!start out.pdf")

@apply_functions_for_expand+=
if self.name == "det" then
	local exp_add
	assert(#fargs == 1, "det() expected 1 argument")
	local t1 = fargs[1]
	assert(t1.kind == "matexp", "det() expected matrix, found " .. t1.kind)
	assert(t1.n == t1.m, "det() expected square matrix")
	@compute_matrix_determinant
	return add_exp
end

@declare_functions+=
local function computeDeterminant(rows, n, i, taken, add_exp, mul_exp)
	if i > n then
		add_exp = (add_exp and AddExpression(add_exp, mul_exp)) or mul_exp
	end

	local sign = true

	for j=1,n do
		if not taken[j] then
			taken[j] = true
			local cell = vim.deepcopy(rows[i][j])
			if not sign then 
				cell = PrefixSubExpression(cell)
			end
			local next_mul = (mul_exp and MulExpression(vim.deepcopy(mul_exp), vim.deepcopy(cell))) or vim.deepcopy(cell)
			add_exp = computeDeterminant(rows, n, i+1, taken, add_exp, next_mul)
			taken[j] = false
			sign = not sign
		end
	end
	return add_exp
end

@compute_matrix_determinant+=
local taken = {}
add_exp = computeDeterminant(t1.rows, t1.n, 1, taken)
