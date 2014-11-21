-- lutem - lua template engine
-- @Copyright  Daly
--

--node type define
local NODE_TEXT = 1
local NODE_FOR = 2
local NODE_EXPR = 3
local NODE_BLOCK = 4
local NODE_RAW = 5

ast_node = {
	node_type = NODE_BLOCK, 
	child_ = {},
	parent_ = nil,

	lno_ = 0,     --start line no 
	content = "", --raw content, different nodes has different meaning
}

lutem = {
	output_ = {},     --render output buffer
	state_ = 0,      --finish parsing or not
	args_ = {},

	lineno_ = 0,    --line count
	node_root_ = nil,     --block
	blocks_ = {},

	involve_file_ = {}, 
	file_queue_ = {},   --inherit by extends
	path_root_ = "./",
}


--utils 将t1中的值全部保存进一个表中
local function obj_copy(t1)
	local tb = {}
	for k,v in pairs(t1) do 
		if type(v) == "table" then 
			tb[k] = obj_copy(v) 
		else	
			tb[k] = v 
		end
	end
	return tb
end

--生成一个新的 ast_node，并将 ntype,parent,content 赋予它
local function new_ast_node(ntype, parent, content)
	tb = obj_copy(ast_node)
	tb.parent_ = parent
	tb.node_type = ntype
	tb.content = content
	return tb
end

--类方法 new，初始化 lutem 类中的所有元数据
function lutem:new()
	local o = {}
	o.output_ = {}   
	o.args_ = {}
	o.node_root_ = nil  
	o.blocks_ = {}
	o.involve_file_ = {} 
	o.file_queue_ = {} 

	setmetatable(o, self)
	self.__index = self
	return o
end

-- parse command in {% %}
-- return: (cmd, arglist)
-- 	  cmd --  command name
-- 	  arglist -- an array of arglist(according to command)
-- 分析字符串，从中获得命令字符串以及包含的可迭代对象以及变量。
local function parse_instr(s)
	local nf = 0
	local cmd = nil                     --保存命令字符串，arr_token 中的第一个字符串
	local arglist = {}	            -- 保存可迭代的对象或变量
	local arr_token = {}                --保存非空字符串
	for f in string.gmatch(s, "([^ \t\r\n]+)") do --匹配非空字符，例如空格、制表符、回车等，s 是字符串
		table.insert(arr_token, f)  --将获取的非空字符串保存进arr_token 表
		nf = nf + 1                 --计数器+1
	end
	--check token
	if nf < 1 then return "", -1 end    --如果字符串中不含非空字符串，则返回空串和-1
	cmd = arr_token[1]                  --从 arr_token 表中获取第一个字符串作为命令字符串
	if cmd == "for" then                --如果 cmd 是 "for"字符串
		if nf ~= 4 and nf ~= 5 then return "",{} end  --如果计数器不为4或5，那么返回空串和空表
		if arr_token[nf-1] ~= "in" then return "",{} end  --如果 arr_token 中倒数第二个字符串不是"in"，返回空串和空表
		if nf == 5 then             --若计数器为5
			--maybe has space between iter key and value, join them
			table.insert(arglist, arr_token[2]..arr_token[3]) --将 arr_token 中第二个和第三个合并，插入 arglist
		else 
			table.insert(arglist, arr_token[2]) --否则将第二个插入 arglist 中
		end

		table.insert(arglist, arr_token[nf]) --将 arr_token 中最后一个插入 arglist 中
	elseif cmd == "endfor" or cmd == "endblock" then --如果cmd 为"endfor"或"endblock"
		--no param
		if nf > 1 then return "",{} end  --若计数器大于1，返回空串和空表
	elseif cmd == "extend" or cmd == "block" then --如果 cmd 为"extend"或"block"
		--only 1 param
		if nf > 2 then return "",{} end --若计数器大于2，那么返回空串和空表
		table.insert(arglist, arr_token[2]) --将 arr_token 中第二个元素插入 arglist 表中
	end
	return cmd, arglist --返回命令字符串和 arglist 表
end


local function print_node(node, prefix)
	if node.node_type == NODE_FOR then  --若节点类型为 NODE_FOR
		print(prefix .. " " .. node.content[2]) --打印"prefix+node.content[2]"
	else                                -- 否则
		print(prefix .. " " .. node.content) -- 打印"prefix+node.content"
	end
end

--类方法，parse_file
function lutem:parse_file(filename, path)
	srclines = {}    --HTML 文件按行存储入 srclines 表
	local f, err = io.open(self.path_root_..filename, 'r')
	if f == nil then return -1,"parse file error "..filename  end

	for line in f:lines() do
		table.insert(srclines, line .. "\n") --将文件安行保存入 srclines 表
	end
	f:close()

	--compile it
	local node = nil
	local extend_from = nil
	--cur_block 为一个类型为 NODE_BLOCK 的，父节点为 nil 的，内容为"__root"的新节点
	local cur_block = new_ast_node(NODE_BLOCK, nil, "__root")
	-- 父节点 cur_parent 为 cur_block
	local cur_parent = cur_block
	-- cur_text 为一个类型为 NODE_TEXT，父节点为 cur_parent，内容为空串的新节点
	local cur_text = new_ast_node(NODE_TEXT, cur_parent, "")
	-- 块"__root"为 cur_parent
	self.blocks_["__root"] = cur_parent
	self.node_root_ = cur_parent
	
	local cur_lno = 1  --当前行号
	local lex_bstart = '{[{%%]'  -- {%或{{
	local pos_s, pos_e, pos_tmp
	local last = 1
	local i,j
	local bstack = {}  --block / for stack 
	local pre, word, cmd, arglist 
	local skip_block = 0
	table.insert(bstack, cur_parent)
	for lno,text in ipairs(srclines) do
		while (last <= #text) do --逐个分析 srclines 中每个字符串的字符
			--skip extended block
			if skip_block == 1 then 
				i, j = string.find(text, "{%%[ ]*endblock[ ]*%%}", last)
				if i == nil then 
					break 
				else
					last = i
				end
			end

			pos_s = string.find(text, "{[{%%]", last)
			if pos_s == nil then

				if #(cur_text.content) < 1000 then
					cur_text.content = cur_text.content .. string.sub(text, last)
				else 
					table.insert(cur_parent.child_, cur_text)	
					cur_text = new_ast_node(NODE_TEXT, cur_parent, string.sub(text, last))
				end 
				break
			end 

			--while found {{ or {%
			
			cur_text.content = cur_text.content .. string.sub(text, last, pos_s-1)
			table.insert(cur_parent.child_, cur_text)	
			cur_text = new_ast_node(NODE_TEXT, cur_parent, "")
			pre = string.sub(text, pos_s, pos_s + 1)
			last = pos_s + 2
			if pre == '{{' then
				i, j = string.find(text, "[ ]*'[^']+'[ ]*}}", last)
				if i == last then
					word = string.match(text, "'[^']+'", i, j-2)	
					node = new_ast_node(NODE_RAW, cur_parent, string.sub(word, 2, -2))
				else
					i, j = string.find(text, "[ ]*[%w._]+[ ]*}}", last) 
					if i ~= last then return -1, "expr error: "..cur_lno end
					word = string.match(text, "[%w._]+", i, j-2)
					node = new_ast_node(NODE_EXPR, cur_parent, word)
				end
				last = j + 1
				table.insert(cur_parent.child_, node)
			else
				-- parse command
				i, j = string.find(text, "[%w/._%- ]+%%}", last) 
				if i ~= last then return -1, "command error "..cur_lno end
				cmd, arglist = parse_instr(string.sub(text, i, j-2))
				if cmd == "" then return -1, "command syntax error "..cur_lno end
				last = j + 1

				if cmd == "for" then
					node = new_ast_node(NODE_FOR, cur_parent, arglist)
					table.insert(cur_parent.child_, node)
					cur_parent = node
					table.insert(bstack, node)

				elseif cmd == "endfor" then
					if #bstack < 1 or bstack[#bstack].node_type ~= NODE_FOR then
						return -1, "endfor syntax error "..cur_lno 
					end
					table.remove(bstack)	
					cur_parent = bstack[#bstack]
				elseif cmd == "block" then
					if self.blocks_[arglist[1]] ~= nil then
						node = self.blocks_[arglist[1]]
						skip_block = 1
					else
						node = new_ast_node(NODE_BLOCK, cur_parent, arglist[1])
						self.blocks_[arglist[1]] = node
					end
					table.insert(cur_parent.child_, node)
					cur_parent = node
					table.insert(bstack, node)
				elseif cmd == "endblock" then
					if #bstack < 1 or bstack[#bstack].node_type ~= NODE_BLOCK then
						return -1, "endblock error: "..cur_lno
					end
					table.remove(bstack)
					cur_parent = bstack[#bstack]
					skip_block = 0
				elseif cmd == "extend" then
					if self.involved_file ~= nil then
						return -1, "extend duplicated: "..cur_lno
					end 
					if cur_parent.content ~= "__root"
						or #cur_parent.child_ > 2
						or #bstack > 1 then
						return -1, "extend error: "..cur_lno
					end

					table.insert(self.file_queue_, arglist[1])
				end
			end

		--end while
		end

		cur_lno = cur_lno + 1
		last = 1
	end

	table.insert(cur_parent.child_, cur_text)	
	if #bstack > 1 then return -1, print_node(bstack[#bstack], "unmatch block") end
	return 0
end


function lutem:load(filename, path)
	self.involve_file_[filename] = 1
	self.path_root_ = path
	table.insert(self.file_queue_, filename)
	self.queue_pos_ = 1
	while self.queue_pos_ <= #self.file_queue_ do
		local ret,reason = self:parse_file(self.file_queue_[self.queue_pos_])
		if ret == -1 then 
			return -1,reason
		end
		self.queue_pos_ = self.queue_pos_ + 1	
	end
	self.state = 1	
	return 0
end

-- get expression value.
-- support plain variable or table field access
-- Example: {{ varname }}, {{ tbl.sub.field }}
function lutem:get_expr_val(expr)
	local flist = {}
	--table field split by .  e.g:  xxx.yyy.zzz
	for k in string.gmatch(expr, "[%w_]+") do
		table.insert(flist, k)
	end
	-- plain variable
	if #flist == 1 then
		if self.args_[expr] == nil then return "" end
		return tostring(self.args_[expr]) 
	end
	-- table field access
	local val = nil
	local tbl = self.args_
	for _, v in ipairs(flist) do
		if type(tbl) ~= "table" then return "" end
		val = tbl[v]
		if val == nil then return "" end
		tbl = val
	end
	if val == nil or type(val) == "table" then return "" end
	return tostring(val)	
end


function lutem:render_node(node)
	if node.node_type == NODE_TEXT or node.node_type == NODE_RAW then
		table.insert(self.output_, node.content)
	elseif node.node_type == NODE_EXPR then
		table.insert(self.output_, self:get_expr_val(node.content))
	elseif node.node_type == NODE_BLOCK then
		self:render_block(node)
	elseif node.node_type == NODE_FOR then
		self:render_loop(node)
	else
		table.insert(self.output_, node.content)
	end
end

function lutem:render_block(block)
	for _, node in ipairs(block.child_) do
		self:render_node(node)
	end
end

function lutem:render_loop(block)
	iter_tbl = {}
	kname = block.content[1]
	vname = block.content[1]
	tbl_name = block.content[2]
	for k, v in ipairs(self.args_[tbl_name]) do
		table.insert(iter_tbl, {key=k, val=v})
	end
	
	for _, elem in ipairs(iter_tbl) do 
		self.args_[kname] = elem.key
		self.args_[vname] = elem.val
		for _, node in ipairs(block.child_) do
			self:render_node(node)
		end
	end
end

function lutem:render(args)
	if self.state ~= 1 then return "", -1 end
	self.args_ = args
	self:render_block(self.node_root_)
	return table.concat(self.output_, '')
end


return lutem
