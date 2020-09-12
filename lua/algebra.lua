local parseAll

local nocase

local nextToken

local finish

local getToken

local parse

local AddExpression

local PrefixSubExpression

local SubExpression

local MulExpression

local DivExpression

local NumExpression

local SymExpression

local FunExpression

local ExpExpression

local copysign

local countMap

function countMap(a)
	local c = 0
	for _,_ in pairs(a) do
		c = c+1
	end
	return c
end

tokens = {}

events = {}

local token_index

local funs = {
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
	
}

local upper = {}

function AddExpression(left, right) 
	local self = { kind = "addexp", left = left, right = right }
	local collectUpperAddCombine
	
	function self.eval() return self.left.eval() + self.right.eval() end
	function self.expand() 
		local t1 = self.left.expand()
		local t2 = self.right.expand()
		return AddExpression(t1, t2)
	end
	function self.toString() 
		return "(" .. self.left.toString() .. " + " .. self.right.toString() .. ")"
	end
	function collectUpperAddCombine(root, constant, collect, collectPow, rest)
		if root.kind == "addexp" then
			constant = collectUpperAddCombine(root.left, constant, collect, collectPow, rest)
			constant = collectUpperAddCombine(root.right, constant, collect, collectPow, rest)
		else
			local combined = root.combined()
			if combined.kind == "presubexp" then
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
				elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = collect[combined.left.sym] - combined.right.num
				elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
					if not collect[combined.right.sym] then
						collect[combined.right.sym] = 0
					end
					collect[combined.right.sym] = collect[combined.right.sym] - combined.left.num
				elseif combined.kind == "numexp" then
					constant = constant - combined.num
				else
					table.insert(rest, PrefixSubExpression(combined))
				end
				
			else
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
				elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = collect[combined.left.sym] + combined.right.num
				elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
					if not collect[combined.right.sym] then
						collect[combined.right.sym] = 0
					end
					collect[combined.right.sym] = collect[combined.right.sym] + combined.left.num
				else
					table.insert(rest, combined)
				end
				
			end
		end
		return constant
	end
	
	function self.combined() 
		if self.left.kind == "numexp" and self.left.num == 0 then
			return self.right.combined()
		end
		if self.right.kind == "numexp" and self.right.num == 0 then
			return self.left.combined()
		end
		
		local constant = 0
		local collect = {}
		local collectPow = {}
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
		
		local rest = {}
		
		constant = collectUpperAddCombine(self.left, constant, collect, collectPow, rest)
		constant = collectUpperAddCombine(self.right, constant, collect, collectPow, rest)
		
	
		-- print("add constant " .. constant)
		-- print("add collect " .. vim.inspect(collect))
		-- print("add collectPow " .. vim.inspect(storeCollectPow))
		-- print("add rest " .. vim.inspect(rest))
	
		local exp_add
	
		if constant ~= 0 then
			exp_add = NumExpression(constant)
		end
		
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
		
		for _, term in ipairs(rest) do
			if not exp_add then
				exp_add = term
			else
				exp_add = AddExpression(exp_add, term)
			end
		end
		
	
		exp_add = exp_add or NumExpression(0)
		return exp_add
	end
	
return self end

function PrefixSubExpression(left) 
	local self = { kind = "presubexp", left = left }
	function self.eval() return -self.left.eval() end
	
	function self.expand() 
		local t1 = self.left.expand()
		return PrefixSubExpression(t1)
	end
	function self.toString() 
		return "(-" .. self.left.toString() .. ")"
	end
	function self.combined() 
		local t1 = self.left.combined()
		if t1.kind == "presubexp" then
			return t1.left.combined()
		end
		return PrefixSubExpression(t1)
	end
return self end

function SubExpression(left, right)
	local self = { kind = "subexp", left = left, right = right }
	function self.eval() return self.left.eval() - self.right.eval() end
	function self.expand() 
		local t1 = self.left.expand()
		local t2 = self.right.expand()
		return SubExpression(t1, t2)
	end
	function self.toString() 
		return "(" .. self.left.toString() .. " - " .. self.right.toString() .. ")"
	end
	function self.combined() 
		local t1 = self.left.combined()
		local t2 = self.right.combined()
		return SubExpression(t1, t2)
	end
return self end

function MulExpression(left, right)
	local self = { kind = "mulexp", left = left, right = right }
	local collectUpperMul
	
	local collectUpperAddExpand
	
	function self.eval() return self.left.eval() * self.right.eval() end
	function self.expand()
		local collectLeft = {}
		local collectRight = {}
		collectUpperAddExpand(self.left, collectLeft)
		collectUpperAddExpand(self.right, collectRight)
		
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
		
		return exp_add
	end
	
	
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
	
	function self.toString() 
		return "(" .. self.left.toString() .. " * " .. self.right.toString() .. ")"
	end
	function collectUpperMul(root, coeff, collect, rest)
		if root.kind == "mulexp" then
			coeff = collectUpperMul(root.left, coeff, collect, rest)
			coeff = collectUpperMul(root.right, coeff, collect, rest)
		else
			local combined = root.combined()
			if combined.kind == "presubexp" then
				combined = combined.left
				if combined.kind == "symexp" then
					if not collect[combined.sym] then
						collect[combined.sym] = 0
					end
					collect[combined.sym] = copysign(math.abs(collect[combined.sym])+1, collect[combined.sym]*-1)
				elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) + combined.right.num, collect[combined.left.sym]*-1)
				elseif combined.kind == "numexp" then
					coeff = coeff * -combined.num
				elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) * combined.right.num, collect[combined.left.sym]*-1*combined.right.num)
				elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
					if not collect[combined.right.sym] then
						collect[combined.right.sym] = 0
					end
					collect[combined.right.sym] = copysign(math.abs(collect[combined.right.sym]) * combined.left.num, collect[combined.right.sym]*-1*combined.left.num)
				else
					table.insert(rest, PrefixSubExpression(combined))
				end
				
			else
				if combined.kind == "symexp" then
					if not collect[combined.sym] then
						collect[combined.sym] = 0
					end
					collect[combined.sym] = copysign(math.abs(collect[combined.sym])+1, collect[combined.sym])
				elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) + combined.right.num, collect[combined.left.sym])
				elseif combined.kind == "numexp" then
					coeff = coeff * combined.num
				elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) * combined.right.num, collect[combined.left.sym]*combined.right.num)
				elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
					if not collect[combined.right.sym] then
						collect[combined.right.sym] = 0
					end
					collect[combined.right.sym] = copysign(math.abs(collect[combined.right.sym]) * combined.left.num, collect[combined.right.sym]*combined.left.num)
				else
					table.insert(rest, combined)
				end
				
			end
		end
		return coeff
	end
	
	function self.combined() 
		if self.left.kind == "numexp" and self.left.num == 1 then
			return self.right.combined()
		end
		if self.right.kind == "numexp" and self.right.num == 1 then
			return self.left.combined()
		end
		
		if self.left.kind == "numexp" and self.left.num == -1 then
			return (PrefixSubExpression(self.right.combined())).combined()
		end
		if self.right.kind == "numexp" and self.right.num == -1 then
			return (PrefixSubExpression(self.left.combined())).combined()
		end
		
		local collectAll = {}
		local rest = {}
		local coeff = 1
		coeff = collectUpperMul(self.left, coeff, collectAll, rest)
		coeff = collectUpperMul(self.right, coeff, collectAll, rest)
		
		
	
		-- print("mul collectAll " .. vim.inspect(collectAll))
		-- print("mul rest " .. vim.inspect(rest))
		-- print("mul coeff " .. vim.inspect(coeff))
	
		local exp_mul
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
		
		for _, term in ipairs(rest) do
			local exp_pow = term
			if not exp_mul then
				exp_mul = term
			else
				exp_mul = MulExpression(exp_mul, term)
			end
		end
		
		if math.abs(coeff) ~= 1 or (countMap(collectAll) == 0 and #rest == 0) then
			if not exp_mul then
				exp_mul = NumExpression(coeff)
			else
				exp_mul = MulExpression(NumExpression(coeff), exp_mul)
			end
		elseif coeff == -1 then
			exp_mul = PrefixSubExpression(exp_mul)
		end
		
	
		exp_mul = exp_mul or NumExpression(0)
		
		return exp_mul
	end
	
return self end

function DivExpression(left, right)
	local self = { kind = "divexp", left = left, right = right }
	function self.eval() return self.left.eval() / self.right.eval() end
	function self.expand() 
		local t1 = self.left.expand()
		local t2 = self.right.expand()
		return DivExpression(t1, t2)
	end
	function self.toString() 
		return "(" .. self.left.toString() .. " / " .. self.right.toString() .. ")"
	end
	function self.combined() 
		local t1 = self.left.combined()
		local t2 = self.right.combined()
		return DivExpression(t1, t2)
	end
return self end

function NumExpression(num)
	local self = { kind = "numexp", num = num }
	function self.eval() return self.num end
	function self.expand() 
		return NumExpression(self.num)
	end
	function self.toString() 
		return self.num
	end
	function self.combined() 
		return NumExpression(self.num)
	end
return self end

function SymExpression(sym)
	local self = { kind = "symexp", sym = sym }
	function self.eval() return 0 end
	function self.expand() 
		return SymExpression(self.sym) 
	end
	function self.toString() 
		return self.sym
	end
	function self.combined() 
		return SymExpression(self.sym)
	end
return self end

function FunExpression(name, left)
	local self = { kind = "funexp", name = name, left = left }
	function self.eval() return funs[self.name](self.left.eval()) end
	
	function self.expand() 
		local t1 = self.left.expand()
		return FunExpression(self.name, t1) 
	end
	
	function self.toString() 
		return self.name .. "(" .. self.left.toString() .. ")"
	end
	
	function self.combined() 
		local t1 = self.left.combined()
		return NumExpression(self.name, t1)
	end
return self end

function ExpExpression(left, right)
	local self = { kind = "expexp", left = left, right = right }
	function self.eval() return math.pow(self.left.eval(), self.right.eval()) end
	
	function self.toString() 
		return "(" .. self.left.toString() .. " ^ " .. self.right.toString() .. ")"
	end
	function self.expand() 
		if self.right.kind == "numexp" and math.floor(self.right.num) == self.right.num and self.right.num > 1 then
			local term1 = vim.deepcopy(self.left)
			local term2
			if self.right.num > 2 then
				term2 = ExpExpression(vim.deepcopy(self.left), NumExpression(self.right.num-1))
			else 
				term2 = vim.deepcopy(self.left)
			end
			local exp = MulExpression(term1, term2)
			return exp.expand()
			
		else
			return self 
		end
	end
	
	function self.combined() 
		local t1 = self.left.combined()
		local t2 = self.right.combined()
		return ExpExpression(t1, t2)
	end
return self end

-- closure-based object
local function AddToken() local self = { kind = "add" }
	function self.prefix()
		return parse(self.priority())
	end
	
	function self.infix(left)
		local t = parse(self.priority())
		if not t then
			return nil
		end
		return AddExpression(left, t)
	end
	function self.priority() return 50 end
	
return self end
local function SubToken() local self = { kind = "sub" }
	function self.prefix()
		local t = parse(90)
		if not t then
			return nil
		end
		return PrefixSubExpression(t)
	end
	
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
	
return self end
local function MulToken() local self = { kind = "mul" }
	function self.infix(left)
		local t = parse(self.priority())
		if not t then
			return nil
		end
		return MulExpression(left, t)
	end
	function self.priority() return 60 end
	
return self end
local function DivToken() local self = { kind = "div" }
	function self.infix(left)
		local t = parse(self.priority()+1)
		if not t then
			return nil
		end
		return DivExpression(left, t)
	end
	function self.priority() return 60 end
	
return self end

local function RParToken() local self = { kind = "rpar" }
	function self.priority() return 10 end
	
return self end
local function LParToken() local self = { kind = "lpar" }
	function self.prefix()
		local exp = parse(20)
		if not exp then
			return nil
		end
		local rpar = nextToken()
		if not rpar or rpar.kind ~= "rpar" then 
			table.insert(events, "Unmatched '('")
			return nil
		end
		
		return exp
	end
	
	function self.priority() return 100 end
	
	function self.infix(left)
		local exp = parse(20)
		if not exp then
			return nil
		end
		local rpar = nextToken()
		if not rpar or rpar.kind ~= "rpar" then 
			table.insert(events, "Unmatched '('")
			return nil
		end
		
		local name = left.sym
		return FunExpression(name, exp)
	end
	
return self end

local function NumToken(num) local self = { kind = "num", num = num }
	function self.prefix()
		return NumExpression(self.num)
	end
	
return self end

local function SymToken(sym) local self = { kind = "sym", sym = sym }
	function self.prefix()
		return SymExpression(self.sym)
	end
	
return self end

local function ExpToken() local self = { kind = "exp" }
	function self.infix(left)
		local exp = parse(self.priority())
		if not exp then
			return nil
		end
		return ExpExpression(left, exp)
	end
	function self.priority() return 70 end
	
return self end


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

function nextToken()
	local token = tokens[token_index]
	token_index = token_index + 1
	return token
end

function finish()
	return token_index > #tokens
end

function getToken()
	return tokens[token_index]
end

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

function copysign(mag, sign)
	if sign < 0 then
		return -math.abs(mag)
	else
		return math.abs(mag)
	end
end


function parseAll(str)
	tokens = {}
	
	local i = 1
	while i <= string.len(str) do
		local c = string.sub(str, i, i)
		
		if string.match(c, "%s") then
			i = i+1 
		
		elseif c == "+" then table.insert(tokens, AddToken()) i = i+1
		elseif c == "-" then table.insert(tokens, SubToken()) i = i+1
		elseif c == "*" then table.insert(tokens, MulToken()) i = i+1
		elseif c == "/" then table.insert(tokens, DivToken()) i = i+1
		
		elseif c == "^" then table.insert(tokens, ExpToken()) i = i+1
		
		elseif c == "(" then table.insert(tokens, LParToken()) i = i+1
		elseif c == ")" then table.insert(tokens, RParToken()) i = i+1
		
		elseif string.match(c, "%d") then 
			local parsed = string.match(string.sub(str, i), "%d+%.?%d*")
			i = i+string.len(parsed)
			table.insert(tokens, NumToken(tonumber(parsed))) 
		
		elseif string.match(c, "%a") then
			if #tokens > 0 and tokens[#tokens].kind == "num" then
				table.insert(tokens, MulToken())
			end
			
			local parsed = string.match(string.sub(str, i), "%a+")
			i = i+string.len(parsed)
			
			if string.match(parsed, "^" .. nocase("pi") .. "$") then
				table.insert(tokens, NumToken(3.14159265258979))
			elseif string.match(parsed, "^" .. nocase("e") .. "$") then
				table.insert(tokens, NumToken(2.71828182845905))
			
			else
				table.insert(tokens, SymToken(parsed))
			end
			
		
		else
			table.insert(events, "Unexpected character insert " .. c)
			i = i+1
		end
		
	end
	
	token_index = 1
	
	local exp = parse(0)
	
	return exp
end

local function expand()
	local line = vim.api.nvim_get_current_line()
	
	local exp = parseAll(line)
	if not exp then
		return
	end
	
	-- @print_result
	local expanded = exp.expand()
	print("expanded : " .. expanded.toString())
	
	local combined = expanded.combined()
	print("simplifed " .. combined.toString())
	
end


return {
expand = expand,

}

