local expand

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

local assign

local collectArgs

local isInteger

local function computeDeterminant(rows, n, i, taken, add_exp, mul_exp)
	if i > n then
		add_exp = (add_exp and AddExpression(add_exp, mul_exp)) or mul_exp
	end
	

	local sign = true

	for j=1,n do
		if not taken[j] then
			taken[j] = true
			local cell = rows[i][j].expand()
			if not sign then 
				cell = PrefixSubExpression(cell)
			end
			
			local next_mul = (mul_exp and MulExpression(vim.deepcopy(mul_exp), cell)) or cell
			
			add_exp = computeDeterminant(rows, n, i+1, taken, add_exp, next_mul)
			
			taken[j] = false
			sign = not sign
			
		end
	end
	return add_exp
end

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
	
	cosd = function(x) return math.cos(x*(math.pi/180.0)) end,
	sind = function(x) return math.sin(x*(math.pi/180.0)) end,
	tand = function(x) return math.tan(x*(math.pi/180.0)) end,
	acosd = function(x) return math.acos(x)*(180.0/math.pi) end,
	asind = function(x) return math.asin(x)*(180.0/math.pi) end,
	atand = function(x) return math.atan(x)*(180.0/math.pi) end,
	
}

local upper = {}

symTable = {}

local answerIndex = 1

answer = nil

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
		if self.right.kind == "presubexp" then
			return putParen(self.left, self.priority()) .. "-" .. putParen(self.right.left, self.priority())
		elseif self.right.kind == "numexp" and self.right.num < 0 then
			return putParen(self.left, self.priority()) .. "-" .. putParen(NumExpression(math.abs(self.right.num)), self.priority())
		else
			return putParen(self.left, self.priority()) .. "+" .. putParen(self.right, self.priority())
		end
	end
	function collectUpperAddCombine(root, constant, collect, collectPow, collectMat, rest)
		if root.kind == "addexp" then
			constant = collectUpperAddCombine(root.left, constant, collect, collectPow, collectMat, rest)
			constant = collectUpperAddCombine(root.right, constant, collect, collectPow, collectMat, rest)
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
				elseif combined.kind == "matexp" then
					local rows = {}
					for i=1,combined.m do
						local row = {}
						for j=1,combined.n do
							table.insert(row, PrefixSubExpression(combined.rows[i][j]).combined())
						end
						table.insert(rows, row)
					end
					
					table.insert(collectMat, MatrixExpression(rows, combined.m, combined.n))
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
				elseif combined.kind == "matexp" then
					table.insert(collectMat, combined)
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
		local collectMat = {}
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
		
		constant = collectUpperAddCombine(self.left, constant, collect, collectPow, collectMat, rest)
		constant = collectUpperAddCombine(self.right, constant, collect, collectPow, collectMat, rest)
		
	
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
		
		if #collectMat > 0 then
			if exp_add ~= nil then
				assert(false, "adding matrix with " .. exp_add.toString())
			end
			exp_add = collectMat[1]
			for i=2,#collectMat do
				local m1 = exp_add
				local m2 = collectMat[i]
				rows = {}
				for i=1,m1.m do
					result_row = {}
					for j=1,m1.n do
						table.insert(result_row, AddExpression(m1.rows[i][j], m2.rows[i][j]))
					end
					table.insert(rows, result_row)
				end
				
				exp_add = MatrixExpression(rows, m2.m, m2.n).combined()
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
			return AddExpression(m1, m2)
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
	function self.collectUnknowns(unknowns) 
		self.left.collectUnknowns(unknowns)
		self.right.collectUnknowns(unknowns)
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
			return PrefixSubExpression(m1)
		end
	end
	
	function self.getLeft() 
		return self
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		return PrefixSubExpression(t1, t2)
	end
	function self.collectUnknowns(unknowns) 
		self.left.collectUnknowns(unknowns)
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
			return SubExpression(m1, m2)
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
	function self.collectUnknowns(unknowns) 
		self.left.collectUnknowns(unknowns)
		self.right.collectUnknowns(unknowns)
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
			if combined.kind == "symexp" then
				if not collect[combined.sym] then
					collect[combined.sym] = 0
				end
				collect[combined.sym] = copysign(math.abs(collect[combined.sym])+1, collect[combined.sym])
				
			elseif combined.kind == "expexp" and combined.left.kind == "symexp" and combined.right.kind == "numexp" then
				local sym, num = combined.left.sym, combined.right.num
				if not collect[combined.left.sym] then
					collect[combined.left.sym] = 0
				end
				collect[combined.left.sym] = copysign(math.abs(collect[combined.left.sym]) + combined.right.num, collect[combined.left.sym])
				
			elseif combined.kind == "numexp" then
				coeff = coeff * combined.num
			elseif combined.kind == "matexp" then
				table.insert(collectMat, combined)
			
			else
				table.insert(rest, combined)
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
		
		if self.left.kind == "numexp" and self.left.num == 0 then
			return NumExpression(0)
		end
		if self.right.kind == "numexp" and self.right.num == 0 then
			return NumExpression(0)
		end
		
		local collectAll = {}
		local rest = {}
		local coeff = 1
		local collectMat = {}
		coeff = collectUpperMul(self.left, coeff, collectAll, collectMat, rest)
		coeff = collectUpperMul(self.right, coeff, collectAll, collectMat, rest)
		
		
	
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
		
		if #collectMat > 0 then
			local exp_mat
			exp_mat = collectMat[1]
			for i=2,#collectMat do
				exp_mat = MulExpression(exp_mat, collectMat[i]).combinedMatrix()
			end
			
			if exp_mul then
				local rows = {}
				for i=1,exp_mat.m do
					local new_row = {}
					for j=1,exp_mat.n do
						table.insert(new_row, MulExpression(exp_mul, exp_mat.rows[i][j]).expand().combined())
					end
					table.insert(rows, new_row)
				end
				exp_mul = MatrixExpression(rows, exp_mat.m, exp_mat.n)
				
			else
				exp_mul = exp_mat
			end
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
			table.insert(events, "Matrix mul dimensions mismatch " .. m1.m .. "x" .. m1.n .. " times " .. m2.m .. "x" .. m2.n)
			return
		end
		
		if m1.kind == "matexp" and m2.kind == "matexp" then
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
			
			return MatrixExpression(rows, #rows, #rows[1])
		else
			return MulExpression(m1, m2)
		end
	end
	
	function self.getLeft() 
		return self.left.getLeft()
	end
	function self.substitute() 
		local t1 = self.left.substitute()
		local t2 = self.right.substitute()
		return MulExpression(t1, t2)
	end
	function self.collectUnknowns(unknowns) 
		self.left.collectUnknowns(unknowns)
		self.right.collectUnknowns(unknowns)
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
	function self.collectUnknowns(unknowns) 
		self.left.collectUnknowns(unknowns)
		self.right.collectUnknowns(unknowns)
	end
	function self.combinedMatrix() 
		local t1 = self.left.combinedMatrix()
		local t2 = self.right.combinedMatrix()
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
		return tostring(self.num)
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
	function self.collectUnknowns(unknowns) 
	end
	function self.combinedMatrix() 
		return NumExpression(self.num)
	end
return self end

function SymExpression(sym)
	local self = { kind = "symexp", sym = sym }
	function self.eval() 
		assert(symTable[self.sym], "symbol " .. self.sym .. " does not exist")
		return symTable[self.sym].eval()
	end
	
	
	function self.expand() 
		if symTable[self.sym] then
			return symTable[self.sym].expand()
		end
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
		if symTable[self.sym] and symTable[self.sym].kind == "var" and symTable[self.sym].val.kind ~= "numexp" then
			return symTable[self.sym].val.substitute()
		end
		return self
	end
	function self.collectUnknowns(unknowns) 
		if not symTable[self.sym] then
			unknowns[self.sym] = true
		end
	end
	function self.combinedMatrix() 
		return SymExpression(self.sym)
	end
return self end

function FunExpression(name, args)
	local self = { kind = "funexp", name = name, args = args }
	function self.eval() 
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.eval())
		end
		
		if symTable[self.name] then
			local t1 = symTable[self.name]
			local args = collectArgs(t1)
			
			-- print("arg list " .. vim.inspect(args))
			-- print("t1 " .. vim.inspect(t1))
			-- print("fargs " .. vim.inspect(fargs))
			for i,arg in pairs(args) do
				symTable[arg] = NumExpression(fargs[i])
			end
			
			local res = t1.eval()
			for i,arg in pairs(args) do
				symTable[arg] = nil
			end
			
			return res
		end
		return funs[self.name](unpack(fargs))
	end
	
	function self.arity()
		return #self.args
	end
	
	function self.expand() 
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.expand())
		end
		
		
		if self.name == "grad" then
			assert(#fargs == 1, "grad expects 1 argument found " .. #fargs)
		
			local t1 = fargs[1]
			if t1.kind == "symexp" then
				assert(symTable[t1.sym], t1.sym .. " symbol not found")
				t1 = symTable[t1.sym]
			end
		
			local args = {"x", "y", "z"}
			local rows = {}
			for _,arg in ipairs(args) do
				table.insert(rows, { t1.derive(arg) })
			end
			
			return MatrixExpression(rows, #args, 1).expand().combined()
		end
		
		if self.name == "div" then
			assert(#fargs == 1, "div expects 1 argument found " .. #fargs)
		
			local t1 = fargs[1]
			if t1.kind == "symexp" then
				assert(symTable[t1.sym], t1.sym .. " symbol not found")
				t1 = symTable[t1.sym]
			end
		
			assert(t1.kind == "matexp", "div expects matexp, found " .. t1.kind)
			assert(#t1.rows, "#rows must be 3, found " .. #t1.rows)
		
			local exp_add
			local args = {"x", "y", "z"}
			for _, arg in ipairs(args) do
				local t = t1.derive(arg)
				exp_add = (exp_add and AddExpression(exp_add, t)) or t
			end
			
			return exp_add.expand().combined()
		end
		
		if self.name == "rot" then
			assert(#fargs == 1, "rot expects 1 argument found " .. #fargs)
		
			local t1 = fargs[1]
			if t1.kind == "symexp" then
				assert(symTable[t1.sym], t1.sym .. " symbol not found")
				t1 = symTable[t1.sym]
			end
		
			assert(t1.kind == "matexp", "rot expects matexp argument found " .. t1.kind)
			local args = collectArgs(t1)
			
			assert(#t1.rows == 3, "rot expects 3 rows found " .. #t1.rows)
		
			local rows = {}
			local args = {"x", "y", "z"}
			rows = {}
			rows[1] = { AddExpression(t1.rows[3][1].derive(args[2]), PrefixSubExpression(t1.rows[2][1].derive(args[3]))) }
			rows[2] = { AddExpression(t1.rows[1][1].derive(args[3]), PrefixSubExpression(t1.rows[3][1].derive(args[1]))) }
			rows[3] = { AddExpression(t1.rows[2][1].derive(args[1]), PrefixSubExpression(t1.rows[1][1].derive(args[2]))) }
			
			return MatrixExpression(rows, 3, 1)
		end
		
		if self.name == "laplace" then
			assert(#fargs == 1, "rot expects 1 argument found " .. #fargs)
		
			local t1 = fargs[1]
			if t1.kind == "symexp" then
				assert(symTable[t1.sym], t1.sym .. " symbol not found")
				t1 = symTable[t1.sym]
			end
		
			local args = collectArgs(t1)
			
			local exp_add
			for _, arg in ipairs(args) do
				local t = it.derive(arg).derive(arg)
				exp_add = (exp_add and AddExpression(exp_add, t)) or t
			end
			
			return exp_add
		end
		
		
		if self.name == "det" then
			assert(#fargs == 1, "det() expects 1 argument found " .. #fargs)
		
			local t1 = fargs[1]
			if t1.kind == "symexp" then
				assert(symTable[t1.sym], t1.sym .. " symbol not found")
				t1 = symTable[t1.sym]
			end
		
			assert(t1.kind == "matexp", "det() expected matrix, found " .. t1.kind)
			assert(t1.n == t1.m, "det() expected square matrix found " .. t1.m .. "x" .. t1.n)
		
			local taken = {}
			add_exp = computeDeterminant(t1.rows, t1.n, 1, taken)
			
			return add_exp
		end
		
		if self.name == "transpose" or self.name == "T" then
			assert(#fargs == 1, self.name .. "() expected 1 argument found " .. #fargs)
			local t1 = fargs[1]
			assert(t1.kind == "matexp", self.name .. "() expected matrix, found " .. t1.kind)
			local rows = {}
			for j=1,t1.n do 
				rows[j] = {}
				for i=1,t1.m do 
					rows[j][i] = t1.rows[i][j].expand()
				end
			end
			
			return MatrixExpression(rows, t1.n, t1.m)
		end
		
		if self.name == "dot" then
			assert(#fargs == 2, self.name .. "() expected 2 arguments found " .. #fargs)
			local t1 = fargs[1]
			local t2 = fargs[2]
		
			assert(t1.kind == "matexp", self.name .. "() first argument expected matrix, found " .. t1.kind)
			assert(t2.kind == "matexp", self.name .. "() second argument expected matrix, found " .. t2.kind)
			assert(t1.n == 1, self.name .. "() first argument expected 1 column, found " .. t1.n)
			assert(t2.n == 1, self.name .. "() second argument expected 1 column, found " .. t2.n)
			assert(t1.m == t2.m, self.name .. "() first and second argument expected same column number, found first " .. t1.m .. " and second " .. t2.m)
			local add_exp
			for i=1,t1.m do
				local term = MulExpression(t1.rows[i][1], t2.rows[i][1])
				add_exp = (add_exp and AddExpression(add_exp, term)) or term
			end
			add_exp = add_exp.expand()
			
			return add_exp
		end
		
		if self.name == "cross" then
			assert(#fargs == 2, self.name .. "() expected 2 arguments found " .. #fargs)
			local t1 = fargs[1]
			local t2 = fargs[2]
		
			assert(t1.kind == "matexp", self.name .. "() first argument expected matrix, found " .. t1.kind)
			assert(t2.kind == "matexp", self.name .. "() second argument expected matrix, found " .. t2.kind)
			assert(t1.n == 1, self.name .. "() first argument expected 1 column, found " .. t1.n)
			assert(t2.n == 1, self.name .. "() second argument expected 1 column, found " .. t2.n)
			assert(t1.m == 3, self.name .. "() first argument expected 3 column, found " .. t1.m)
			assert(t2.m == 3, self.name .. "() first argument expected 3 column, found " .. t2.m)
			local rows = {}
			rows[1] = { AddExpression(MulExpression(t1.rows[2][1].expand(),t2.rows[3][1].expand()), PrefixSubExpression(MulExpression(t1.rows[3][1].expand(),t2.rows[2][1].expand()))) }
			rows[2] = { AddExpression(MulExpression(t1.rows[3][1].expand(),t2.rows[1][1].expand()), PrefixSubExpression(MulExpression(t1.rows[1][1].expand(),t2.rows[3][1].expand()))) }
			rows[3] = { AddExpression(MulExpression(t1.rows[1][1].expand(),t2.rows[2][1].expand()), PrefixSubExpression(MulExpression(t1.rows[2][1].expand(),t2.rows[1][1].expand()))) }
			return MatrixExpression(rows, 3, 1)
		end
		
		return FunExpression(self.name, fargs) 
	end
	
	function self.toString() 
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.toString())
		end
		return self.name .. "(" .. table.concat(fargs, ", ") .. ")"
	end
	
	function self.combined() 
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.combined())
		end
		return FunExpression(self.name, fargs)
	end
	
	function self.derive(sym) 
		if self.name == "" then
		elseif self.name == "cos" then
			-- -sin(u)*u'
			local l = FunExpression("sin", vim.deepcopy(self.args[1]))
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
			local l = FunExpression("cos", vim.deepcopy(self.args[1]))
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
			local t1 = self.args[1].derive(sym)
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
	
	
	function self.getLeft() 
		return self
	end
	function self.substitute() 
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.substitute())
		end
		return FunExpression(self.name, fargs)
	end
	function self.collectUnknowns(unknowns) 
		for _,arg in ipairs(self.args) do
			arg.collectUnknowns(unknowns)
		end
	end
	function self.combinedMatrix() 
		local fargs = {}
		for _,arg in ipairs(self.args) do
			table.insert(fargs, arg.combinedMatrix())
		end
		return FunExpression(self.name, fargs)
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
	function self.collectUnknowns(unknowns) 
		self.left.collectUnknowns(unknowns)
		self.right.collectUnknowns(unknowns)
	end
	function self.combinedMatrix() 
		local t1 = self.left.combinedMatrix()
		local t2 = self.right.combinedMatrix()
		if t2.kind == "numexp" and isInteger(t2.num) and  t2.num > 1 then
			local tomult = MulExpression(t1, ExpExpression(vim.deepcopy(t1), NumExpression(t2.num-1)))
			return tomult.combinedMatrix()
			
		elseif t2.kind == "numexp" and t2.num == 1 then
			return t1
		end
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
	
	
	function self.collectUnknowns(unknowns) 
		for i=1,self.m do
			for j=1,self.n do
				self.rows[i][j].collectUnknowns(unknowns)
			end
		end
	end
	
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
	
	function self.eval()
		local new_rows = {}
		for _,row in ipairs(self.rows) do
			local new_cells = {}
			for _,cell in ipairs(row) do
				table.insert(new_cells, cell.eval())
			end
			table.insert(new_rows, new_cells)
		end
		return MatrixExpression(new_rows, self.m, self.n)
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
		local args = {}
		while not finish() do
			local exp = parse(20)
			if not exp then
				return nil
			end
			table.insert(args, exp)
			local t = nextToken()
			if t.kind == "rpar" then
				break
			end
			
			assert(t.kind == "comma", "expected comma in function arg list")
			
		end
		local name = left.sym
		return FunExpression(name, args)
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
		
		elseif string.match(c, "[%a_]") then
			if #tokens > 0 and tokens[#tokens].kind == "num" then
				table.insert(tokens, MulToken())
			end
			
			local parsed = string.match(string.sub(str, i), "[%w_]+")
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
		print(name .. " := " .. sym.toString())
	end
end

function collectArgs(exp)
	local unknowns = {}
	exp.collectUnknowns(unknowns)

	local args = {}
	for arg,_ in pairs(unknowns) do
		table.insert(args, arg)
	end
	table.sort(args)
	return args
end

function isInteger(x)
	return math.floor(x) == x
end


function parseAll(str)
	tokenize(str)
	token_index = 1
	
	local exp = parse(0)
	
	return exp
end

function expand(line)
	local exp = parseAll(line)
	if not exp then
		return
	end
	
	answer = exp
	symTable["answer"] = exp
	
	local res = exp.substitute().expand().combined()
	local line = res.toString()
	vim.api.nvim_buf_set_lines(0, -1, -1, true, { line })
	
end


function assign(line)
	local i1, i2 = string.find(line, ":=")
	assert(i1, "expected :=")
	
	local left = string.sub(line, 1, i1-1)
	tokenize(left)
	
	local symEntry
	assert(#tokens == 1, "variable name expected token")
	assert(tokens[1].kind == "sym", "variable name expected symbol")
	local name = tokens[1].sym
	
	local right = string.sub(line, i2+1)
	local exp = parseAll(right)
	if not exp then
		return
	end
	
	exp = exp.substitute().expand().combined()
	print(name .. " := " .. exp.toString())
	
	symTable[name] = exp
	
end

function simplify()
	local line = vim.api.nvim_get_current_line()
	
	if string.match(line, ":=") then
		assign(line)
	
	else
		expand(line)
	end
	
end

function evaluate()
	local line = vim.api.nvim_get_current_line()
	
	local exp = parseAll(line)
	if not exp then
		return
	end
	
	answer = exp
	symTable["answer"] = exp
	
	local res = tostring(exp.eval())
	vim.api.nvim_buf_set_lines(0, -1, -1, true, { res })
	
end

local function show_latex()
	local line = vim.api.nvim_get_current_line()
	
	local exp = parseAll(line)
	if not exp then
		return
	end
	
	f = io.open("out.tex", "w")
	f:write("\\documentclass[a4paper]{slides}\n")
	f:write("\\begin{document}\n")
	f:write("$" .. exp.toLatex() .. "$\n")
	f:write("\\end{document}\n")
	f:close()
	vim.api.nvim_command("!pandoc out.tex -o out.pdf")
	vim.api.nvim_command("!start out.pdf")
	
end


return {
printSymTable = printSymTable,

simplify = simplify,

evaluate = evaluate,

show_latex = show_latex,

}

