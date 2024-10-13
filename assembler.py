import sys
import os
import time
import argparse
import ast
import copy
import pickle
import gzip
import lark

def checkArgs():
	argparser = argparse.ArgumentParser()
	argparser.add_argument("infile", help="Source file to read assembly instructions from.")
	argparser.add_argument("-o", "--outfile", default=os.path.join(os.getcwd(), "a.out"), help="Write object file to OUTFILE. Default is \"a.out\".")
	argparser.add_argument("-w", "--warning-level", default = 1, type = int, help="Stop assembly process if a warning is encountered, as if an error had occurred. Levels increase from 1 (errors only) to 3 (info, warnings, and errors).")
	argparser.add_argument("-v", "--verbose", action = "count", default = 1, help = "Specify once to show messages from warnings and twice to show messages from info.")
	argparser.add_argument("-i", "--include-dirs", nargs="+", action="extend", default = [], help="Search the given directories when an INCLUDE directive is used with no path.")
	
	result = argparser.parse_args()
	
	if result.warning_level > 3:
		result.warning_level = 3
	if result.warning_level < 1:
		result.warning_level = 1
	result.warning_level -= 1
	
	
	if result.verbose > 3:
		result.verbose = 3
	result.verbose -= 1
	
	i = 0
	while i < len(result.include_dirs):
		result.include_dirs[i] = os.path.abspath(result.include_dirs[i])
		i += 1
	
	result.infile = os.path.abspath(result.infile)
	result.outfile = os.path.abspath(result.outfile)
	return result

def createParser(cpu):
	myGrammar = cpu["grammar"] + "REGISTER.1: "
	for regname in cpu["registers"]:
		myGrammar += "\"" + regname + "\"i | "
	myGrammar += "\"$r\" NUMBER*\nKEYWORD.1: "
	for keyw in cpu["keywords"]:
		myGrammar += "\"" + keyw + "\"i | "
	myGrammar = myGrammar[0:-3]
	
	return lark.Lark(grammar = myGrammar, start = "head", propagate_positions = True, parser = "lalr", lexer = "contextual")

def parseFile(infile, incDirs, ctxt, caps):
	cwd = os.getcwd()
	infile = os.path.abspath(infile)
	os.chdir(os.path.dirname(infile))
	
	try:
		text = getContents(infile) + "\n"
	except (FileNotFoundError, PermissionError, OSError):
		err(ctxt, P46Error("Could not read file \"" + infile + "\".", "stdin", -1, -1, 0))
	
	try:
		tree = ctxt.parser.parse(text)
	except lark.exceptions.UnexpectedInput as e:
		err(ctxt, P46Error("Syntax error.\n" + e.get_context(text)[0:-1], infile, e.line, e.column, 0))
	
	caps.visit(tree)
	pass0(tree, infile, incDirs, ctxt, caps)	
	os.chdir(cwd)

def getContents(path):
	text = ""
	try:
		infile = open(path, "r")
		text = infile.read()
	except Exception as e:
		raise e
	else:
		infile.close()
		return text

def verifyInstruction(ctxt, inst, file):
	keyw = inst.children[0]
	args = inst.children[1].children
	
	fmt = P46["formats"][P46["keywords"][keyw.value]]
	
	i = 0
	while i < len(fmt):
		if i >= len(args):
			err(ctxt, P46Error(keyw + " keyword requires " + str(len(fmt)) + " arguments, but only " + str(len(args)) + " were given.", file, keyw.line, keyw.column, 0))
		
		if fmt[i] == "array":
			i = -1
			break
		elif fmt[i] != "any":
			if fmt[i] != args[i].data:
				err(ctxt, P46Error("Argument #" + str(i+1) + " of \"" + keyw + "\" must be of type \"" + fmt[i] + "\", but \"" + args[i].data + "\" was given.", file, args[i].meta.line, args[i].meta.column, 0))
		i += 1
	
	if (len(fmt) != len(args)) and i >= 0:
		err(ctxt, P46Error(keyw + " keyword uses " + str(len(fmt)) + " arguments, but " + str(len(args)) + " were given.", file, args[i].meta.line, args[i].meta.column, 1))

def pass0(tree, filename, incDirs, ctxt, caps):
	stmt = None
	inst = None
	lbls = None
	i = -1
	
	ctxt.instructions.append(lark.Tree("statement", [lark.Tree("instruction", ["FILE", lark.Tree("", [filename])])]))
	
	while i < len(tree.children) - 1:
		i += 1
	
		stmt = tree.children[i]
		lbls, inst = separateInstruction(stmt)
		
		if not inst:
			ctxt.labelBuf.extend(lbls)
			continue
			
		keyw = inst.children[0]
		args = inst.children[1].children
			
		if keyw == "MACRO":
			i += readMacro(tree.children, i, args[0].children[0], filename, ctxt)
			continue
		
		verifyInstruction(ctxt, inst, filename)
					
		if keyw == "INCLUDE":
			try:
				parseFile(getFileFromString(ctxt, incDirs, filename, args[0].children[0]), incDirs, ctxt, caps)
			except P46Error as e:
				err(ctxt, P46Error("", filename, inst.meta.line, inst.meta.column, 0, e))
			continue
		
		
		if len(ctxt.labelBuf) != 0:
			ctxt.labelBuf.extend(stmt.children)
			stmt.children = ctxt.labelBuf
			ctxt.labelBuf = []
		
		ctxt.instructions.append(stmt)
	
	ctxt.instructions.append(lark.Tree("statement", [lark.Tree("instruction", ["FILE", lark.Tree("", [0])])]))

def pass1(filename0, ctxt):
	PC = 0
	rel = True
	visitorSym = SymbolReplacer()
	visitorMac = MacroReplacer()
	lastSeenLabel = []
	fileStack = [filename0]
	lblBuf = []
	i = 0
	
	while i < len(ctxt.instructions):
		stmt = ctxt.instructions[i]
		lbls, inst = separateInstruction(stmt)
		
		trackQualifiedNames(lastSeenLabel, lbls, ctxt, PC, fileStack[-1], rel, lblBuf)
		visitorSym.updateLabels(inst, lastSeenLabel)
		
		keyw = inst.children[0]
		args = inst.children[1].children
		
		match(keyw):
			case "INVOKE":
				insertMacro(ctxt, i, args, visitorMac, fileStack[-1])
				continue
			case "REPEAT":
				insertRept(ctxt, i, args, PC, fileStack[-1])
				continue
			case "ENDR":
				err(ctxt, P46Error("\"ENDR\" encountered outside of a REPEAT block.", fileStack[-1], keyw.line, keyw.column, 0))
			case "IF":
				insertIf(ctxt, i, args, PC, fileStack[-1])
				continue
			case "ELIF" | "ELSE" | "ENDC":
				err(ctxt, P46Error("\"" + keyw + "\" encountered outside of an IF block.", fileStack[-1], keyw.line, keyw.column, 0))
			case "SET":
				setSymbol(ctxt, i, args, fileStack[-1])
			case "FILE":
				if args[0] == 0:
					fileStack.pop()
				else:
					fileStack.append(args[0])
			case "LABEL":
				lblBuf.extend(args[0])
				del ctxt.instructions[i]
				continue
			case "ORG":
				PC = evaluateExpr(args[0])
				rel = False
				del ctxt.instructions[i]
				continue
			case "PRINT":
				print(getStringFromString(args[0]))
			case "RESERVE":
				PC += evaluateExpr(args[0])
			case "DATAB":
				PC += len(args)
			case "DATAH":
				PC += len(args) << 1
			case "DATAW":
				PC += len(args) << 2
			case _:
				if PC & 3:
					err(ctxt, P46Error("Instruction not aligned to a word boundary.", fileStack[-1], keyw.line, keyw.column, 1))
				PC += 4
			
		ctxt.result.append(inst)
		i += 1
	
	trackQualifiedNames(lastSeenLabel, ctxt.labelBuf, ctxt, PC, fileStack[-1], rel, lblBuf)
	
	for sym in ctxt.sets:
		del ctxt.symbols[sym]

def setSymbol(ctxt, idx, args, file):
	sym = args[0].children[0]
	value = evaluateExpr(args[1], ctxt, None, False, file)
	
	if value == None:
		err(ctxt, P46Error("Symbol \"" + sym + "\" is unknown at assemble time.", sym.line, sym.column, 2))
	
	ctxt.sets[sym] = value
	ctxt.symbols[sym] = value

def getNumber(tree, ctxt, PC, demand, file):
	token = tree.children[0]
	match tree.data:
		case "integer":
			return Symbol(int(token.value, 0), False)
		case "symbol":
			if token.value in ctxt.symbols:
				result = ctxt.symbols[token.value]
				if result.value != None:
					return result
			if demand:
				err(ctxt, P46Error("Symbol \"" + token.value + "\" was referenced before being given a value.", file, token.line, token.column, 0))
			return Symbol(None, True)
		case "program_counter":
			return Symbol(PC, True)
		case _:
			return evaluateExpr(tree, ctxt, PC, demand, file)

def evaluateExpr(expr, ctxt, PC, demand, file):
	if len(expr.children) == 1:
		return getNumber(expr, ctxt, PC, demand, file)
	
	if expr.data == "unary_expr":
		lhs = Symbol(0, False)
		op = expr.children[0]
		rhs = getNumber(expr.children[1], ctxt, PC, demand, file)
	else:
		lhs = getNumber(expr.children[0], ctxt, PC, demand, file)
		op = expr.children[1]
		rhs = getNumber(expr.children[2], ctxt, PC, demand, file)
	
	match op:
		case "+":
			return Symbol(lhs.value + rhs.value, lhs.isRelative or rhs.isRelative)
		case "-":
			return Symbol(lhs.value - rhs.value, lhs.isRelative != rhs.isRelative)
		case "~":
			return Symbol(-1 ^ rhs.value, rhs.isRelative)
		case "*":
			return Symbol(lhs.value * rhs.value, lhs.isRelative or rhs.isRelative)
		case "/":
			return Symbol(lhs.value // rhs.value, lhs.isRelative or rhs.isRelative)
		case "%":
			return Symbol(lhs.value % rhs.value, lhs.isRelative or rhs.isRelative)
		case "&":
			return Symbol(lhs.value & rhs.value, lhs.isRelative or rhs.isRelative)
		case "|":
			return Symbol(lhs.value | rhs.value, lhs.isRelative or rhs.isRelative)
		case "^":
			return Symbol(lhs.value ^ rhs.value, lhs.isRelative or rhs.isRelative)
		case "==":
			return Symbol(1 if (lhs.value == rhs.value) else 0, lhs.isRelative != rhs.isRelative)
		case "!=":
			return Symbol(1 if (lhs.value != rhs.value) else 0, lhs.isRelative != rhs.isRelative)
		case "<":
			return Symbol(1 if (lhs.value < rhs.value) else 0, lhs.isRelative != rhs.isRelative)
		case ">=":
			return Symbol(1 if (lhs.value >= rhs.value) else 0, lhs.isRelative != rhs.isRelative)
		case ">":
			return Symbol(1 if (lhs.value > rhs.value) else 0, lhs.isRelative != rhs.isRelative)
		case "<=":
			return Symbol(1 if (lhs.value <= rhs.value) else 0, lhs.isRelative != rhs.isRelative)
		case "&&":
			return Symbol(((lhs.value != 0) and (rhs.value != 0)), lhs.isRelative or rhs.isRelative)
		case "||":
			return Symbol(((lhs.value != 0) or (rhs.value != 0)), lhs.isRelative or rhs.isRelative)
		case "^^":
			return Symbol(((lhs.value != 0) + (rhs.value != 0) == 1), lhs.isRelative or rhs.isRelative)

def insertMacro(ctxt, idx, args, visitor, file):
	visitor.initialize(args)
	
	macroContents = copy.deepcopy(ctxt.macros[args[0].children[0]])
	for line in macroContents:
		visitor.visit(line)
		verifyInstruction(ctxt, separateInstruction(line)[1], file)
	
	i = visitor.usedAll()
	if i:
		err(ctxt, P46Error("Macro \"" + args[0].children[0] + "\" demands " + str(len(args)-1) + " arguments, but did not consume #" + str(i) + ".", file, args[i].meta.line, args[i].meta.column, 1))
	
	ctxt.instructions[idx:idx+1] = macroContents

def insertRept(ctxt, base, args, PC, file):
	contents = []
	nestDepth = 1
	i = 1
	N = evaluateExpr(args[0], ctxt, PC, True, file).value
	
	while (base+i) < len(ctxt.instructions):
		x = separateInstruction(ctxt.instructions[base + i])[1].children[0]
		if x == "REPEAT":
			nestDepth += 1
		if x == "ENDR":
			nestDepth -= 1
			if nestDepth == 0:
				break
		
		contents.append(ctxt.instructions[base+i])
		i += 1
		
	if (base+i) == len(ctxt.instructions):
		err(ctxt, P46Error("REPEAT block was never terminated.", file, args[0].meta.line, args[0].meta.column, 0))
	
	ctxt.instructions[base:base+i+1] = contents*N

def insertIf(ctxt, base, args, PC, file):
	contents = []
	nestDepth = 1
	i = 1
	
	conditionMet = evaluateExpr(args[0], ctxt, PC, True, file).value
	
	while (not conditionMet and ((base+i) < len(ctxt.instructions))):
		inst = separateInstruction(ctxt.instructions[base + i])[1]
		x = inst.children[0]
		
		if x == "IF":
			nestDepth += 1
		elif x == "ENDC":
			nestDepth -= 1
			if nestDepth == 0:
				break
		
		if nestDepth == 1:
			if x == "ELIF":
				conditionMet = evaluateExpr(inst.children[1].children[0], ctxt, PC, True, file).value
			if x == "ELSE":
				conditionMet = True

		i += 1
	
	#at this point "i" points to the first instruction that should be included
	#if no conditions were met, "i" points to the ENDC.
	
	nestDepth = 1
	
	while (base+i) < len(ctxt.instructions):
		x = separateInstruction(ctxt.instructions[base + i])[1].children[0]
		
		if x == "IF":
			nestDepth += 1
		if x == "ENDC":
			nestDepth -= 1
			if nestDepth == 0:
				break
		
		contents.append(ctxt.instructions[base+i])
		i += 1
	
	if (base+i) == len(ctxt.instructions):
		err(ctxt, P46Error("IF block was never terminated.", file, args[0].meta.line, args[0].meta.column, 0))
	
	ctxt.instructions[base:base+i+1] = contents

def trackQualifiedNames(prevLbl, curLbls, ctxt, LC, filename, isRel, lblBuf):
	if len(lblBuf) > 0:
		lblBuf.extend(curLbls)
		curLbls = lblBuf
	
	for lblT in curLbls:
		lbl = lblT.children[0]
		tmp = lbl.split(".")
		periodScan = False
	
		for i in range(len(tmp)):
			if tmp[i] == "":
				if periodScan:
					err(ctxt, P46Error("Sublabel \"" + lbl + "\" mixes relative and absolute modes.", filename, lbl.line, lbl.column, 0))
				if i >= len(prevLbl):
					err(ctxt, P46Error("Sublabel \"" + lbl + "\" declared with no parent.", filename, lbl.line, lbl.column, 0))
				tmp[i] = prevLbl[i]
			else:
				periodScan = True
			
		result = ".".join(tmp)
		
		if result in ctxt.symbols:
			err(ctxt, P46Error("Symbol \"" + lbl + "\" is multiply defined.", filename, lbl.line, lbl.column, 0))
		sym = Symbol(LC, isRel)
		ctxt.symbols[result] = sym
		if lbl.type == "exported_label":
			ctxt.exports[result] = sym
		
		prevLbl[:] = tmp
	
	lblBuf.clear()
	
def separateInstruction(statement):
	l = []
	i = None
	for child in statement.children:
		if child.data == "exported_label" or child.data == "internal_label":
			l.append(child)
		elif child.data == "instruction":
			i = child
			break
		else:
			break
	return l, i

def readMacro(statements, base, name, file, ctxt):
	contents = []
	lblBuf = []
	i = 1
	
	if name in ctxt.macros:
		err(ctxt, P46Error("Macro \"" + name + "\" previously defined.", file, statements[base].meta.line, statements[base].meta.column, 0))
	
	while (base + i) < len(statements):
		lbls, inst = separateInstruction(statements[base + i])
		
		if not inst:
			lblBuf.extend(lbls)
			i += 1
			continue
		
		keyw = inst.children[0]
		
		if keyw == "MACRO":
			err(ctxt, P46Error("Macro \"" + name + "\" was never terminated.", file, statements[base].meta.line, statements[base].meta.column, 0))
		if keyw == "ENDM":
			break
		
		if len(lblBuf) > 0:
			labelBuf.extend(stmt.children)
			stmt.children = labelBuf
			labelBuf = []
		
		contents.append(statements[base + i])
		i += 1
		
	if (base+i) == len(statements):
		err(ctxt, P46Error("Macro \"" + name + "\" was never terminated.", file, statements[base].meta.line, statements[base].meta.column, 0))
	
	if len(lblBuf) > 0:
		err(ctxt, P46Error("Macro \"" + name + "\" contains a trailing label.", file, statements[base].meta.line, statements[base].meta.column, 2))
		ctxt.instructions.append(lark.Tree("statement", [lark.Tree("instruction", ["LABEL", lark.Tree("", [lblBuf])])]))
	ctxt.macros[name] = contents
	return i

def getStringFromString(s):
	return ast.literal_eval(s)

def getFileFromString(ctxt, dirs, file, s):
	literal = getStringFromString(s)
	if len(literal) > 0:
		if literal[0] == "<" and literal[-1] == ">":
			l = literal[1:-1]
			for prefix in dirs:
				if os.path.isfile(os.path.join(prefix, l)):
					return os.path.abspath(os.path.join(prefix, l))
			err(ctxt, P46Error("Could not locate \"" + literal + "\" in given INCLUDE directories.", file, s.line, s.column, 0))
	return literal

def output(outfile, ctxt):
	outfile = os.path.abspath(outfile)
	result = dict([ ("instructions", ctxt.result), ("exports", ctxt.exports), ("symbols", ctxt.symbols) ])
	
	try:
		fileObj = gzip.open(outfile, "wb")
		pickle.dump(result, fileObj)
	except (FileNotFoundError, PermissionError, OSError):
		err(ctxt, P46Error("Could not write file " + outfile, "stdout", -1, -1, 0))
	finally:
		fileObj.close()	

def err(ctxt, e):
	if e.lvl <= ctxt.w:
		raise e
	if e.lvl <= ctxt.v:
		printErrors(e)

def printErrors(e, lvl = 0):
	s = "  "*lvl
	
	match e.lvl:
		case 0:
			s += "ERROR"
		case 1:
			s += "WARNING"
		case 2:
			s += "INFO"
	
	s += " in " + e.file
	if e.line >= 0:
		s += ", line " + str(e.line)
	if e.col >= 0:
		s += ", column " + str(e.col)
	s += ":"
	print(s)
	if e.child:
		printErrors(e.child, lvl+1)
	else:
		print("  "*(lvl+1) + e.msg)

def printCtxt(ctxt):
	for i in ctxt.instructions:
		x = i.children[-1]
		print(x.children[0])
	for s in ctxt.symbols:
		print(s + ": " + str(ctxt.symbols[s].value))

def main():
	print()
	arglist = checkArgs()	
	myParser = createParser(P46)
	myCtxt = ASMContext(arglist.warning_level, arglist.verbose, myParser)
	try:
		parseFile(arglist.infile, arglist.include_dirs, myCtxt, Capitalizer())
		pass1(arglist.infile, myCtxt)
		output(arglist.outfile, myCtxt)
		print("Assembly succeeded with 0 errors.")
	except P46Error as e:
		printErrors(e)
	else:
		printCtxt(myCtxt)
	print()
	
###############################

P46 = dict([
	("registers",
		["R0","AT","V0","V1","A0","A1","A2","A3","T0","T1","T2","T3","T4","T5","T6","T7","S0","S1","S2","S3","S4","S5","S6","S7","K0","K1","K2","K3","P0","P1","SP","RA"]),
	
	("keywords",
	dict([
		("ADD","R"), ("SUB","R"), ("AND","R"), ("OR","R"), ("XOR","R"), ("SLL","R"), ("SRL","R"), ("SRA","R"), ("SLT","R"), ("SLTU","R"), ("ADDI","I"), ("RSUBI","I"), ("ANDI","I"), ("ORI","I"), ("XORI","I"), ("SLLI","I"), ("SRLI","I"), ("SRAI","I"), ("SLTI","I"), ("SLTIU","I"), ("BEQ","I"), ("BNE","I"), ("BLT","I"), ("BLTU","I"), ("BGE","I"), ("BGEU","I"), ("J","J"), ("JAL","J"), ("JRALR","D"), ("LUI","L"), ("PCOFF","L"), ("MFHI","S"), ("MFLO","S"), ("LB","M"), ("LBU","M"), ("LH","M"), ("LHU","M"), ("LW","M"), ("SB","M"), ("SH","M"), ("SW","M"), ("MUL","D"), ("MULU","D"), ("DIV","D"), ("DIVU","D"), ("MULI","D"), ("MULIU","D"), ("DIVI","D"), ("DIVIU","D"),
	
		("NOP","N"), ("MOV","D"), ("LDR","L"), ("INC","S"), ("DEC","S"), ("NEG","S"), ("NOT","S"), ("SGT","R"), ("SLE","R"), ("ABS","D"), ("ROL","R"), ("ROLI","I"), ("MULT","R"), ("MULTI","I"), ("DIVV","R"), ("DIVVI","I"), ("MOD","R"), ("JR","S"), ("JRAL","S"), ("B","J"), ("BGT","I"), ("BLE","I"), ("BEQZ","L"), ("BNEZ","L"), ("BLTZ","L"), ("BGEZ","L"), ("BGTZ","L"), ("BLEZ","L"), ("IN","L"), ("OUT","L"),
	
		("INCLUDE","F"), ("INVOKE","V"), ("MACRO","Y"), ("ENDM","N"), ("REPEAT","J"), ("ENDR","N"), ("IF","J"), ("ELIF","J"), ("ELSE","N"), ("ENDC","N"), ("RESERVE","J"), ("DATAB","A"), ("DATAH","A"), ("DATAW","A"), ("ORG","J"), ("SET","T"), ("PRINT","F")
	])),
	
	("formats",
	dict([
		("N", []),
		("S", ["register"]),
		("D", ["register","register"]),
		("R", ["register","register","register"]),
		("J", ["any"]),
		("L", ["register","any"]),
		("I", ["register","register","any"]),
		("M", ["register","memory_access"]),
		("F", ["string"]),
		("A", ["array"]),
		("Y", ["symbol"]),
		("V", ["symbol", "array"]),
		("T", ["symbol", "any"])
	])),
	
	("grammar",
"""head: statement*

statement: label* instruction? _COMMENT? _NEWLINE

label: IDENTIFIER ":"  -> internal_label
     | IDENTIFIER "::" -> exported_label

instruction: KEYWORD arglist
arglist: (expression ("," expression)*)?

?expression: binary_expr | unary_expr

?binary_expr: comparison (LOGIC_OP expression)?
?comparison: bitstring (COMP_OP expression)?
?bitstring: addition (BIT_OP expression)?
?addition: multiplication (ADD_OP expression)?
?multiplication: atom (MUL_OP expression)?
?unary_expr: UNARY_OP expression

?atom: NUMBER -> integer
     | STRING -> string
     | IDENTIFIER -> symbol
     | REGISTER -> register
	 | "@" -> program_counter
     | "[" REGISTER (ADD_OP expression)? "]" -> memory_access
     | IDENTIFIER "(" arglist ")" -> function_call
     | "(" expression ")"
	 | "#" NUMBER* -> macro_argument

LOGIC_OP: "&&" | "||" | "^^"
COMP_OP: "==" | "!=" | "<" | ">=" | ">" | "<="
BIT_OP: "&" | "|" | "^"
ADD_OP: "+" | "-"
MUL_OP: "*" | "/" | "%"
UNARY_OP: "+" | "-" | "~"

HEXDIGIT: "a".."f" | "A".."F" | DIGIT
DIGIT: "0".."9"
LETTER: "a".."z" | "A".."Z"
NUMBER: DIGIT DIGIT* | "0x" HEXDIGIT HEXDIGIT* | "0X" HEXDIGIT HEXDIGIT*
STRING: "\\"" /([^"\\\\]|\\\\.)*/ "\\""
IDENTIFIER: ("_" | LETTER | ".") ("_" | LETTER | DIGIT | ".")*

_COMMENT: /;[^\\n]*/
_NEWLINE: "\\r"? "\\n"
WHITESPACE: " " | "\\t" | "\\v" | "\\f" | "\\b"
%ignore WHITESPACE

""")
	])

###############################

class P46Error(Exception):
	def __init__(self, message, f, l, c, level, child=None):
		self.msg = message
		self.file = f
		self.line = l
		self.col = c
		self.lvl = level
		self.child = child

class ASMContext:
	def __init__(self, warnings, verbose, parser):
		self.instructions = []
		self.macros = dict()
		self.parser = parser
		self.exports = dict()
		self.symbols = dict()
		self.sets = dict()
		self.labelBuf = []
		self.result = []
		self.w = warnings
		self.v = verbose

class SymbolReplacer(lark.visitors.Visitor_Recursive):
	def __init__(self):
		self.lblBuf = []
		
	def updateLabels(self, instruction, lbl):
		self.lblBuf = lbl
		self.visit(instruction)
	
	def symbol(self, x):
		sym = x.children[0].split(".")
		periodScan = False
		for i in range(len(sym)):
			if sym[i] == "":
				if periodScan:
					P46Error("Sublabel \"" + x.children[0] + "\" mixes relative and absolute modes.", file, x.meta.line, x.meta.column)
				if i >= len(self.lblBuf):
					raise P46Error("Sublabel \"" + x.children[0] + "\" references nonexistent parent.", file, x.meta.line, x.meta.column)
				sym[i] = self.lblBuf[i]
			else:
				periodScan = True
		
		x.children[0] = x.children[0].update(value = ".".join(sym))

class MacroReplacer(lark.visitors.Visitor_Recursive):
	def __init__(self):
		self.args = []
		self.used = []
	
	def initialize(self, args):
		self.args = args
		self.used = [False]*len(self.args)
		self.used[0] = True
	
	def macro_argument(self, y):
		x = y.children[0]
		idx = int(x.value)
		
		if idx >= len(self.args):
			raise P46Error("Macro \"" + self.args[0].children[0] + "\" demands argument " + x + " but only " + str(len(self.args)-1) + " were given.", file, self.args[-1].line, self.args[-1].column)
		
		self.used[idx] = True
		y.data = self.args[idx].data
		y.children = self.args[idx].children
	
	def usedAll(self):
		i = 0
		while i < len(self.used):
			if self.used[i] == False:
				return i
			i += 1
		return 0

class Capitalizer(lark.visitors.Visitor_Recursive):	
	def instruction(self, x):
		x.children[0] = x.children[0].update(value = x.children[0].value.upper())
	
	def register(self, x):
		x.children[0] = x.children[0].update(value = x.children[0].value.upper())

class Symbol:
	def __init__(self, value, rel):
		self.value = value
		self.isRelative = rel

###############################

main()