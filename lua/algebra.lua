local parseAll

local tokenize

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

local putParen

local copysign

local countMap

function countMap(a)
	local c = 0
	for _,_ in pairs(a) do
		c = c+1
	end
	return c
end

local isZero

local isOne

local putParenLatex

tokens = {}

events = {}

local token_index

local priority_list = {
	["add"] = 50,
	
	["sub"] = 50,
	
	["mul"] = 60,
	
	["div"] = 70,
	
	["lpar"] = 100,
	
	["rpar"] = 10,
	
	["exp"] = 70,
	
	["presub"] = 90,
	["exp"] = 90,
	["sym"] = 110,
	["num"] = 110,
	["fun"] = 100,
	
	["rbra"] = 5,
	["comma"] = 5,
	["semi"] = 5,
	
	["mat"] = 110,
	
}

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

symTable = {}

local answerIndex = 1

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
		return putParen(self.left, self.priority()) .. ((self.right.kind == "presubexp" and ("-" .. putParen(self.right.left, self.priority()))) or ("+" .. putParen(self.right, self.priority())))
	end
	function collectUpperAddCombine(root, constant, collect, collectPow, rest)
		if root.kind == "addexp" then
			constant = collectUpperAddCombine(root.left, constant, collect, collectPow, rest)
			constant = collectUpperAddCombine(root.right, constant, collect, collectPow, rest)
		else
			local combined = root.combined()
			if combined.kind == "presubexp" then
				combined = combined.left
				local factor = -1
				if combined.kind == "symexp" then
					if not collect[combined.sym] then
						collect[combined.sym] = 0
					end
					collect[combined.sym] = collect[combined.sym] + factor*1
					
				elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					local powpair = {combined.left.sym, combined.right.num}
					if not collectPow[powpair] then
						collectPow[powpair] = 0
					end
					collectPow[powpair] = collectPow[powpair] + factor*1
					
				elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					local sym, num = combined.left.sym, combined.right.num
					if not collect[sym] then
						collect[sym] = 0
					end
					collect[sym] = collect[sym] + factor*num
					
				elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
					local sym, num = combined.right.sym, combined.left.num
					if not collect[sym] then
						collect[sym] = 0
					end
					collect[sym] = collect[sym] + factor*num
					
				elseif combined.kind == "mulexp" and combined.left.kind == "expexp" and combined.right.kind == "numexp" then
					if combined.left.left.kind == "symexp" and combined.left.right.kind == "numexp" then
						local sym, pow, num = combined.left.left.sym, combined.left.right.num, combined.right.num
						local powpair = {sym, pow}
						if not collectPow[powpair] then
							collectPow[powpair] = 0
						end
						collectPow[powpair] = collectPow[powpair] + factor*num
						
					end
				elseif combined.kind == "mulexp" and combined.right.kind == "expexp" and combined.left.kind == "numexp" then
					if combined.right.left.kind == "symexp" and combined.right.right.kind == "numexp" then
						local sym, pow, num = combined.right.left.sym, combined.right.right.num, combined.left.num
						local powpair = {sym, pow}
						if not collectPow[powpair] then
							collectPow[powpair] = 0
						end
						collectPow[powpair] = collectPow[powpair] + factor*num
						
					end
				elseif combined.kind == "numexp" then
					constant = constant - combined.num
				else
					table.insert(rest, PrefixSubExpression(combined))
				end
				
			else
				local factor = 1
				if combined.kind == "symexp" then
					if not collect[combined.sym] then
						collect[combined.sym] = 0
					end
					collect[combined.sym] = collect[combined.sym] + factor*1
					
				elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					local powpair = {combined.left.sym, combined.right.num}
					if not collectPow[powpair] then
						collectPow[powpair] = 0
					end
					collectPow[powpair] = collectPow[powpair] + factor*1
					
				elseif combined.kind == "numexp" then
					constant = constant + combined.num
				elseif combined.kind == "mulexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					local sym, num = combined.left.sym, combined.right.num
					if not collect[sym] then
						collect[sym] = 0
					end
					collect[sym] = collect[sym] + factor*num
					
				elseif combined.kind == "mulexp" and combined.left.kind == "numexp" and combined.right.kind == "symexp" then
					local sym, num = combined.right.sym, combined.left.num
					if not collect[sym] then
						collect[sym] = 0
					end
					collect[sym] = collect[sym] + factor*num
					
				elseif combined.kind == "mulexp" and combined.left.kind == "expexp" and combined.right.kind == "numexp" then
					if combined.left.left.kind == "symexp" and combined.left.right.kind == "numexp" then
						local sym, pow, num = combined.left.left.sym, combined.left.right.num, combined.right.num
						local powpair = {sym, pow}
						if not collectPow[powpair] then
							collectPow[powpair] = 0
						end
						collectPow[powpair] = collectPow[powpair] + factor*num
						
					end
				elseif combined.kind == "mulexp" and combined.right.kind == "expexp" and combined.left.kind == "numexp" then
					if combined.right.left.kind == "symexp" and combined.right.right.kind == "numexp" then
						local sym, pow, num = combined.right.left.sym, combined.right.right.num, combined.left.num
						local powpair = {sym, pow}
						if not collectPow[powpair] then
							collectPow[powpair] = 0
						end
						collectPow[powpair] = collectPow[powpair] + factor*num
						
					end
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
	
	function self.derive(sym) 
		local t1 = self.left.derive(sym)
		local t2 = self.right.derive(sym)
	
		if isZero(t1) then return t2 end
		if isZero(t2) then return t1 end
	
		return AddExpression(t1, t2)
	end
	function self.priority() 
		return priority_list["add"]
	end
	function self.toLatex() 
		return putParen(self.left, self.priority()) .. ((self.right.kind == "presubexp" and ("-" .. putParen(self.right.left, self.priority()))) or ("+" .. putParen(self.right, self.priority())))
	end
	function self.combinedMatrix()
		local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
		local m2 = (self.right.combinedMatrix and self.right.combinedMatrix()) or self.right
		if m1.kind == "matexp" and m2.kind == "matexp" then
			if m1.m ~= m2.m or m1.n ~= m2.n then
				table.insert(events, "add matrix dimensions mismatch")
				return
			end
			
			rows = {}
			for i=1,m1.m do
				result_row = {}
				for j=1,m1.n do
					table.insert(result_row, AddExpression(m1.rows[i][j], m2.rows[i][j]))
				end
				table.insert(rows, result_row)
			end
			
			return MatrixExpression(rows)
		else
			return self
		end
	end
	
	function self.getLeft() 
		return self.left.getLeft()
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		local t2 = self.right.substitute()
		return AddExpression(t1, t2)
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
		return "-" .. putParen(self.left, self.priority()) .. ""
	end
	function self.combined() 
		local t1 = self.left.combined()
		if t1.kind == "presubexp" then
			return t1.left.combined()
		elseif isZero(t1) then
			return t1.combined()
		end
		return PrefixSubExpression(t1)
	end
	function self.derive(sym) 
		local t1 = self.left.derive(sym)
		if isZero(t1) then return t1 end
		return PrefixSubExpression(t1)
	end
	function self.priority() 
		return priority_list["presub"]
	end
	function self.toLatex() 
		return "-" .. putParenLatex(self.left, self.priority()) .. ""
	end
	function self.combinedMatrix()
		local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
		if m1.kind == "matexp" then
			rows = {}
			for i=1,m1.m do
				result_row = {}
				for j=1,m1.n do
					table.insert(result_row, PrefixSubExpression(m1.rows[i][j]))
				end
				table.insert(rows, result_row)
			end
			
			return MatrixExpression(rows)
		else
			return self
		end
	end
	
	function self.getLeft() 
		return self
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		return PrefixSubExpression(t1, t2)
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
		return putParen(self.left, self.priority()) .. "-" .. putParen(self.right, self.priority())
	end
	function self.combined() 
		local t1 = self.left.combined()
		local t2 = self.right.combined()
		return SubExpression(t1, t2)
	end
	function self.derive(sym) 
		local t1 = self.left.derive(sym)
		local t2 = self.right.derive(sym)
	
		if isZero(t1) then return PrefixSubExpression(t2) end
		if isZero(t2) then return t1 end
	
		return SubExpression(t1, t2)
	end
	function self.priority() 
		return priority_list["sub"]
	end
	function self.toLatex() 
		return putParenLatex(self.left, self.priority()) .. "-" .. putParenLatex(self.right, self.priority())
	end
	function self.combinedMatrix()
		local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
		local m2 = (self.right.combinedMatrix and self.right.combinedMatrix()) or self.right
		if m1.kind == "matexp" and m2.kind == "matexp" then
			if m1.m ~= m2.m or m1.n ~= m2.n then
				table.insert(events, "add matrix dimensions mismatch")
				return
			end
			
			rows = {}
			for i=1,m1.m do
				result_row = {}
				for j=1,m1.n do
					table.insert(result_row, SubExpression(m1.rows[i][j], m2.rows[i][j]))
				end
				table.insert(rows, result_row)
			end
			
			return MatrixExpression(rows)
		else
			return self
		end
	end
	
	function self.getLeft() 
		return self.left.getLeft()
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		local t2 = self.right.substitute()
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
		if self.left.kind == "numexp" and self.right.getLeft().kind ~= "numexp" then
			return putParen(self.left, self.priority()) .. putParen(self.right, self.priority())
		else 
			return putParen(self.left, self.priority()) .. "*" .. putParen(self.right, self.priority())
		end
	end
	function collectUpperMul(root, coeff, collect, rest)
		if root.kind == "mulexp" then
			coeff = collectUpperMul(root.left, coeff, collect, rest)
			coeff = collectUpperMul(root.right, coeff, collect, rest)
		else
			local combined = root.combined()
			if combined.kind == "presubexp" then
				combined = combined.left
				local factor = -1
				if combined.kind == "symexp" then
					if not collect[combined.sym] then
						collect[combined.sym] = 0
					end
					collect[combined.sym] = copysign(math.abs(collect[combined.sym])+1, collect[combined.sym]*factor)
					
				elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					local sym, num = combined.left.sym, combined.right.num
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) + combined.right.num, collect[combined.left.sym]*factor)
					
				elseif combined.kind == "numexp" then
					coeff = coeff * -combined.num
				else
					table.insert(rest, PrefixSubExpression(combined))
				end
				
			else
				local factor = 1
				if combined.kind == "symexp" then
					if not collect[combined.sym] then
						collect[combined.sym] = 0
					end
					collect[combined.sym] = copysign(math.abs(collect[combined.sym])+1, collect[combined.sym]*factor)
					
				elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
					local sym, num = combined.left.sym, combined.right.num
					if not collect[combined.left.sym] then
						collect[combined.left.sym] = 0
					end
					collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) + combined.right.num, collect[combined.left.sym]*factor)
					
				elseif combined.kind == "numexp" then
					coeff = coeff * combined.num
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
	function self.priority() 
		return priority_list["mul"]
	end
	function self.toLatex() 
		if self.left.kind == "numexp" and self.right.kind ~= "numexp" then
			return putParenLatex(self.left, self.priority()) .. putParenLatex(self.right, self.priority())
		else
			return putParenLatex(self.left, self.priority()) .. " \\cdot " .. putParenLatex(self.right, self.priority())
		end
	end
	function self.combinedMatrix()
		local m1 = (self.left.combinedMatrix and self.left.combinedMatrix()) or self.left
		local m2 = (self.right.combinedMatrix and self.right.combinedMatrix()) or self.right
		if m1.m ~= m2.n or m1.n ~= m2.m then
			table.insert(events, "Matrix mul dimensions mismatch")
			return
		end
		
		rows = {}
		for i=1,m2.n do
			for j=1,m1.m do
				local cell
				for k=1,m1.n do
					local exp = MulExpression(m1.rows[j][k], m2.rows[k][i])
					cell = (not cell and exp) or AddExpression(cell, exp)
				end
				
				if not rows[j] then
					rows[j] = {}
				end
				rows[j][i] = cell
				
			end
		end
		
		return MatrixExpression(rows)
	end
	
	function self.getLeft() 
		return self.left.getLeft()
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		local t2 = self.right.substitute()
		return MulExpression(t1, t2)
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
		return putParen(self.left, self.priority()) .. "/" .. putParen(self.right, self.priority())
	end
	function self.combined() 
		local t1 = self.left.combined()
		local t2 = self.right.combined()
		return DivExpression(t1, t2)
	end
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
	function self.priority() 
		return priority_list["div"]
	end
	function self.toLatex() 
		return "\\frac{" .. self.left.toLatex() .. "}{" .. self.right.toLatex() .. "}"
	end
	function self.getLeft() 
		return self.left.getLeft()
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		local t2 = self.right.substitute()
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
	function self.derive(sym) 
		return NumExpression(0)
	end
	function self.priority() 
		return priority_list["num"]
	end
	function self.toLatex() 
		return self.num
	end
	function self.getLeft() 
		return self
	end
	function self.substitute() 
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
	function self.derive(sym) 
		if self.sym == sym then 
			return NumExpression(1) 
		else return NumExpression(0) end
	end
	function self.priority() 
		return priority_list["sym"]
	end
	function self.toLatex() 
		return self.sym
	end
	function self.getLeft() 
		return self
	end
	function self.substitute() 
		if symTable[self.sym] then
			return symTable[self.sym].val.substitute()
		end
		return self
	end
return self end

function FunExpression(name, left)
	local self = { kind = "funexp", name = name, left = left }
	function self.eval() return funs[self.name](self.left.eval()) end
	
	function self.expand() 
		local t1 = self.left.expand()
		print("t1: " .. t1.toString())
		if self.name == "grad" and t1.kind == "symexp" then
			if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
				local symEntry = symTable[t1.sym]
				local args = symEntry.args
				assert(symEntry.val.kind ~= "matexp")
				local rows = {}
				for _, arg in ipairs(args) do
					table.insert(rows, { symEntry.val.derive(arg) })
				end
				
				local newSymEntry = {
					name = answerIndex,
					kind = "fun",
					args = args,
					val = MatrixExpression(rows, #args, 1)
				}
				answerIndex = answerIndex + 1
				symTable[newSymEntry.name] = newSymEntry
				
				return SymExpression(newSymEntry.name)
			end
		end
		
		if self.name == "div" and t1.kind == "symexp" then
			if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
				local symEntry = symTable[t1.sym]
				local args = symEntry.args
				local exp_add
				assert(symEntry.val.kind ~= "matexp")
				for _, arg in ipairs(args) do
					local t = symEntry.val.derive(arg)
					exp_add = (exp_add and AddExpression(exp_add, t)) or t
				end
				
				local newSymEntry = {
					name = answerIndex,
					kind = "fun",
					args = args,
					val = exp_add
				}
				answerIndex = answerIndex + 1
				symTable[newSymEntry.name] = newSymEntry
				
				return SymExpression(newSymEntry.name)
			end
		end
		
		if self.name == "rot" and t1.kind == "symexp" then
			print("apply rot to " .. t1.sym)
			local arg
			if symTable[t1.sym] and symTable[t1.sym].kind == "fun" then
				local symEntry = symTable[t1.sym]
				local args = symEntry.args
		
				assert(symEntry.val.kind == "matexp")
				assert(symEntry.val.m == 3 and symEntry.val.n == 1)
		
				local rows = {}
				rows = {}
				local mat = symEntry.val
				rows[1] = { AddExpression(mat.rows[3][1].derive(args[2]), PrefixSubExpression(mat.rows[2][1].derive(args[3]))) }
				rows[2] = { AddExpression(mat.rows[1][1].derive(args[3]), PrefixSubExpression(mat.rows[3][1].derive(args[1]))) }
				rows[3] = { AddExpression(mat.rows[2][1].derive(args[1]), PrefixSubExpression(mat.rows[1][1].derive(args[2]))) }
				local newSymEntry = {
					name = answerIndex,
					kind = "fun",
					args = args,
					val = MatrixExpression(rows, #args, 1)
				}
				answerIndex = answerIndex + 1
				symTable[newSymEntry.name] = newSymEntry
				
				return SymExpression(newSymEntry.name)
			end
		end
		
		return FunExpression(self.name, t1) 
	end
	
	function self.toString() 
		return self.name .. "(" .. self.left.toString() .. ")"
	end
	
	function self.combined() 
		local t1 = self.left.combined()
		return FunExpression(self.name, t1)
	end
	
	function self.derive(sym) 
		if self.name == "" then
		elseif self.name == "cos" then
			-- -sin(u)*u'
			local l = FunExpression("sin", vim.deepcopy(self.left))
			local t1 = self.left.derive(sym)
			local p = MulExpression(l, t1)
			if isZero(t1) then
				return t1
			elseif isOne(t1) then
				p = l
			end
			return PrefixSubExpression(p)
		elseif self.name == "sin" then
			-- cos(u)*u'
			local l = FunExpression("cos", vim.deepcopy(self.left))
			local t1 = self.left.derive(sym)
			local p = MulExpression(l, t1)
			if isZero(t1) then
				return t1
			elseif isOne(t1) then
				p = l
			end
			return p
		elseif self.name == "sqrt" then
			-- u'/(2*sqrt(u))
			local t1 = self.left.derive(sym)
			if isZero(t1) then
				return t1
			end
		
			local p = MulExpression(NumExpression(2), vim.deepcopy(self))
			local d = DivExpression(t1, p)
			return d
		
		else 
			table.insert(events, "Unknown function " .. self.name)
		end
	end
	
	function self.priority() 
		return priority_list["fun"]
	end
	function self.toLatex() 
		return "\\" .. self.name .. "{" .. self.left.toLatex() .. "}"
	end
	
	function self.getLeft() 
		return self
	end
	function self.substitute() 
		return FunExpression(self.name, self.left.substitute())
	end
return self end

function ExpExpression(left, right)
	local self = { kind = "expexp", left = left, right = right }
	function self.eval() return math.pow(self.left.eval(), self.right.eval()) end
	
	function self.toString() 
		return putParen(self.left, self.priority()) .. "^" .. putParen(self.right, self.priority())
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
		if isOne(t2) then
			return t1
		else
			return ExpExpression(t1, t2)
		end
	end
	function self.derive(sym) 
		-- just support constant number exponents
		if self.right.kind == "numexp" then
			local exp = self.right.num
			if exp == 1 then
				return self.left.derive(sym)
			end
	
			local x = ExpExpression(vim.deepcopy(self.left), NumExpression(exp-1))
			local l = MulExpression(vim.deepcopy(self.right), x)
	
			local t1 = self.left.derive(sym)
			local p = MulExpression(l, t1)
			if isZero(t1) then
				return t1
			elseif isOne(t1) then
				p = l
			end
			return p
		end
	end
	
	function self.priority() 
		return priority_list["exp"]
	end
	function self.toLatex() 
		return putParenLatex(self.left, self.priority()) .. "^" .. putParenLatex(self.right, self.priority())
	end
	function self.getLeft() 
		return self.left.getLeft()
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		local t2 = self.right.substitute()
		return ExpExpression(t1, t2)
	end
return self end

function MatrixExpression(rows, m, n)
	local self = { kind = "matexp", rows = rows, m = m, n = n }
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
	
	function self.priority() 
		return priority_list["mat"]
	end
	function self.getLeft() 
		return self
	end
	
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
	function self.priority() return priority_list["add"] end
	
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
	function self.priority() return priority_list["sub"] end
	
return self end
local function MulToken() local self = { kind = "mul" }
	function self.infix(left)
		local t = parse(self.priority())
		if not t then
			return nil
		end
		return MulExpression(left, t)
	end
	function self.priority() return priority_list["mul"] end
	
return self end
local function DivToken() local self = { kind = "div" }
	function self.infix(left)
		local t = parse(self.priority()+1)
		if not t then
			return nil
		end
		return DivExpression(left, t)
	end
	function self.priority() return priority_list["div"] end
	
return self end

local function RParToken() local self = { kind = "rpar" }
	function self.priority() return priority_list["rpar"] end
	
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
	
	function self.priority() return priority_list["lpar"] end
	
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
	function self.priority() return priority_list["exp"] end
	
return self end

-- right bracket
local function LBraToken() local self = { kind = "lbra" }
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
			if t.kind == "rbra" then
				break
			end
			
			if t.kind == "comma" then
				j = j+1
			end
			
			if t.kind == "semi" then
				rows[#rows+1] = {}
				i = i+1
				j = 1
			end
			
		end
		local curlen
		for _,row in ipairs(rows) do
			if not curlen then
				curlen = #row
			end
		
			if #row ~= curlen then
				table.insert(events, "matrix dimension incorrect")
			end
		end
		
		local exp = MatrixExpression(rows, #rows, curlen)
		
		return exp
	end
	
return self end
-- left bracket
local function RBraToken() local self = { kind = "rbra" }
	function self.priority() return priority_list["rbra"] end
return self end
-- comma
local function CommaToken() local self = { kind = "comma" }
	function self.priority() return priority_list["comma"] end
return self end
-- semi-colon
local function SemiToken() local self = { kind = "semi" }
	function self.priority() return priority_list["semi"] end
return self end


function tokenize(str)
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
		
		elseif c == "[" then table.insert(tokens, LBraToken()) i = i+1
		elseif c == "]" then table.insert(tokens, RBraToken()) i = i+1
		elseif c == "," then table.insert(tokens, CommaToken()) i = i+1
		elseif c == ";" then table.insert(tokens, SemiToken()) i = i+1
		
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
	
end

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

function putParen(exp, p)
	if exp.priority() < p then
		return "(" .. exp.toString() .. ")"
	else
		return exp.toString()
	end
end

function copysign(mag, sign)
	if sign < 0 then
		return -math.abs(mag)
	else
		return math.abs(mag)
	end
end

function isZero(exp)
	if exp.kind == "numexp" and exp.num == 0 then
		return true
	elseif exp.kind == "matexp" then
		for i=1,exp.m do
			for j=1,exp.n do
				if not isZero(exp.rows[i][j]) then
					return false
				end
			end
		end
		return true
	
	end
	return false
end

function isOne(exp)
	return exp.kind == "numexp" and exp.num == 1
end

function putParenLatex(exp, p)
	if exp.priority() < p then
		return "(" .. exp.toLatex() .. ")"
	else
		return exp.toLatex()
	end
end

local function printSymTable()
	print("Symbol table:")
	for name, sym in pairs(symTable) do
		print(name .. " := " .. sym.val.toString())
	end
end


function parseAll(str)
	tokenize(str)
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
	
	print("parsed: " .. exp.toString())
	
	local expanded = exp.expand()
	print("expanded : " .. expanded.toString())
	
	local combined = expanded.combined()
	table.insert(events, combined.toString())
	print("simplifed " .. combined.toString())
	
	local subst = combined.substitute().expand().combined()
	print("subst " .. subst.toString())
	
	-- @derive_test
	-- @show_latex
end

local function assign()
	local line = vim.api.nvim_get_current_line()
	
	local i1, i2 = string.find(line, ":=")
	assert(i1)
	
	local left = string.sub(line, 1, i1-1)
	tokenize(left)
	
	local symEntry
	if string.find(left, "%(") then
		assert(#tokens > 2)
		assert(tokens[1].kind == "sym")
		local name = tokens[1].sym
		local args = {}
		assert(tokens[2].kind == "lpar")
		i = 2
		while tokens[i] and tokens[i].kind ~= "rpar" do
			i = i + 1
			assert(tokens[i] and tokens[i].kind == "sym")
			table.insert(args, tokens[i].sym)
			i = i + 1
		end
		
		symEntry = {
			name = name,
			kind = "fun",
			args = args
		}
		
	
	else
		assert(#tokens == 1)
		assert(tokens[1].kind == "sym")
		local name = tokens[1].sym
	
		symEntry = {
			name = name,
			kind = "var",
		}
	end
	
	local right = string.sub(line, i2+1)
	local exp = parseAll(right)
	if not exp then
		return
	end
	
	symEntry.val = exp.expand().combined()
	symTable[symEntry.name] = symEntry
	
end


return {
expand = expand,

assign = assign,

printSymTable = printSymTable,

}

