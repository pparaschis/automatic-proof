import math
import numpy as np
from ast import literal_eval

#Just converting the norm tuples into a latex-type string for display purposes - nothing interesting here


class Norm:
	def __init__(self, tup):
		self.tup = tup
		
		self.fncs = tup[0]
		self.ordr = tup[1]
		self.sblv = tup[2]
		self.lbsg = tup[3]


def format_exp(x):
	if x == math.inf:
		return "\\infty"
	try:
		xf = float(x)
		if math.isinf(xf):
			return "\\infty"
		if abs(xf - round(xf)) < 1e-12:
			return str(int(round(xf)))
		return "{:.12g}".format(xf)
	except (TypeError, ValueError):
		return str(x)


def sum_of_norms(norms):

	norm = norms[0]
	tup1 = Norm(norm[0]); tup2 = Norm(norm[1])
	fncs1 = tup1.fncs; fncs2 = tup2.fncs
	ordr1 = tup1.ordr; ordr2 = tup2.ordr
	lbsg1 = tup1.lbsg; lbsg2 = tup2.lbsg
	sblv1 = tup1.sblv; sblv2 = tup2.sblv
	
	splits1 = tup1.fncs.split("*")
	FuncData11 = literal_eval(splits1[0]); FuncData12 = literal_eval(splits1[1])
	ord11 = FuncData11[1]; ord12 = FuncData12[1]
	
	splits2 = tup2.fncs.split("*")
	FuncData21 = literal_eval(splits2[0]); FuncData22 = literal_eval(splits2[1])
	ord21 = FuncData21[1]; ord22 = FuncData22[1]
	
	upart = "{u}".format(u = FuncData11[0]) + "^{{({ord11})}}".format(ord11 = ord11)
	if ord11 == (0, 0): upart = "{u}".format(u = FuncData11[0])
	if FuncData11[0] == '1': upart = ""
	
	vpart = "{v}".format(v = FuncData12[0]) + "^{{({ord12})}}".format(ord12 = ord12)
	if ord12 == (0, 0): vpart = "{v}".format(v = FuncData12[0])
	if FuncData12[0] == '1': vpart = ""
	
	norm1 = "\\|(" + upart + vpart + ")^{{({j})}}\\|".format(j = ordr1)
	if vpart == "": norm1 = "\\|" + upart + "^{{({j})}}\\|".format(j = ordr1)
	if upart == "": norm1 = "\\|" + vpart + "^{{({j})}}\\|".format(j = ordr1)
	
	if ordr1 == (0, 0): norm1 = "\\|" + upart + vpart + "\\|"
	if upart == "" and vpart == "": norm1 = ""
	
		
	pstr1 = format_exp(lbsg1)
	normind1 = "_{{W^{{{k},{p}}}}}".format(k = sblv1, p = pstr1)
	if lbsg1 == 2 and sblv1 > 0: normind1 = "_{{H^{k}}}".format(k = sblv1)
	if sblv1 == 0: normind1 = "_{{L^{{{p}}}}}".format(p = pstr1)
	if lbsg1 == math.inf: normind1 = "_{{W^{{{k},\\infty}}}}".format(k = sblv1)
	if lbsg1 == math.inf and sblv1 == 0: normind1 = "_{{L^\\infty}}"
	if norm1 == "" : normind1 = ""
	
	term1 = norm1 + normind1



	wpart = "{w}".format(w = FuncData21[0]) + "^{{({ord21})}}".format(ord21 = ord21)
	if ord21 == (0, 0): wpart = "{w}".format(w = FuncData21[0])
	if FuncData21[0] == '1': wpart = ""
	
	zpart = "{z}".format(z = FuncData22[0]) + "^{{({ord22})}}".format(ord22 = ord22)
	if ord22 == (0, 0): zpart = "{z}".format(z = FuncData22[0])
	if FuncData22[0] == '1': zpart = ""
	
	norm2 = "\\|(" + wpart + zpart + ")^{{({j})}}\\|".format(j = ordr2)
	if zpart == "": norm2 = "\\|" + wpart + "^{{({j})}}\\|".format(j = ordr2)
	if wpart == "": norm2 = "\\|" + zpart + "^{{({j})}}\\|".format(j = ordr2)
	
	if ordr2 == (0, 0): norm2 = "\\|" + wpart + zpart + "\\|"
	if zpart == "" and wpart == "": norm2 = ""
		
		
	pstr2 = format_exp(lbsg2)
	normind2 = "_{{W^{{{k},{p}}}}}".format(k = sblv2, p = pstr2)
	if lbsg2 == 2 and sblv2 > 0: normind2 = "_{{H^{k}}}".format(k = sblv2)
	if sblv2 == 0: normind2 = "_{{L^{{{p}}}}}".format(p = pstr2)
	if lbsg2 == math.inf: normind2 = "_{{W^{{{k},\\infty}}}}".format(k = sblv2)
	if lbsg2 == math.inf and sblv2 == 0: normind2 = "_{{L^\\infty}}"
	if norm2 == "" : normind2 = ""
	
	term2 = norm2 + normind2
	
	
	result = term1 + term2
	if fncs1 == "('1', (0, 0))*('1', (0, 0))": result = term2
	if fncs2 == "('1', (0, 0))*('1', (0, 0))": result = term1
	final = result
	
	for i in range(1, len(norms)):
	
		norm = norms[i]
		tup1 = Norm(norm[0]); tup2 = Norm(norm[1])
		fncs1 = tup1.fncs; fncs2 = tup2.fncs
		ordr1 = tup1.ordr; ordr2 = tup2.ordr
		lbsg1 = tup1.lbsg; lbsg2 = tup2.lbsg
		sblv1 = tup1.sblv; sblv2 = tup2.sblv
	
		splits1 = tup1.fncs.split("*")
		FuncData11 = literal_eval(splits1[0]); FuncData12 = literal_eval(splits1[1])
		ord11 = FuncData11[1]; ord12 = FuncData12[1]
	
		splits2 = tup2.fncs.split("*")
		FuncData21 = literal_eval(splits2[0]); FuncData22 = literal_eval(splits2[1])
		ord21 = FuncData21[1]; ord22 = FuncData22[1]
	
		upart = "{u}".format(u = FuncData11[0]) + "^{{({ord11})}}".format(ord11 = ord11)
		if ord11 == (0, 0): upart = "{u}".format(u = FuncData11[0])
		if FuncData11[0] == '1': upart = ""
	
		vpart = "{v}".format(v = FuncData12[0]) + "^{{({ord12})}}".format(ord12 = ord12)
		if ord12 == (0, 0): vpart = "{v}".format(v = FuncData12[0])
		if FuncData12[0] == '1': vpart = ""
	
		norm1 = "\\|(" + upart + vpart + ")^{{({j})}}\\|".format(j = ordr1)
		if vpart == "": norm1 = "\\|" + upart + "^{{({j})}}\\|".format(j = ordr1)
		if upart == "": norm1 = "\\|" + vpart + "^{{({j})}}\\|".format(j = ordr1)
	
		if ordr1 == (0, 0): norm1 = "\\|" + upart + vpart + "\\|"
		if upart == "" and vpart == "": norm1 = ""
	
		
		pstr1 = format_exp(lbsg1)
		normind1 = "_{{W^{{{k},{p}}}}}".format(k = sblv1, p = pstr1)
		if lbsg1 == 2 and sblv1 > 0: normind1 = "_{{H^{k}}}".format(k = sblv1)
		if sblv1 == 0: normind1 = "_{{L^{{{p}}}}}".format(p = pstr1)
		if lbsg1 == math.inf: normind1 = "_{{W^{{{k},\\infty}}}}".format(k = sblv1)
		if lbsg1 == math.inf and sblv1 == 0: normind1 = "_{{L^\\infty}}"
		if norm1 == "" : normind1 = ""
	
		term1 = norm1 + normind1



		wpart = "{w}".format(w = FuncData21[0]) + "^{{({ord21})}}".format(ord21 = ord21)
		if ord21 == (0, 0): wpart = "{w}".format(w = FuncData21[0])
		if FuncData21[0] == '1': wpart = ""
	
		zpart = "{z}".format(z = FuncData22[0]) + "^{{({ord22})}}".format(ord22 = ord22)
		if ord22 == (0, 0): zpart = "{z}".format(z = FuncData22[0])
		if FuncData22[0] == '1': zpart = ""
		
		norm2 = "\\|(" + wpart + zpart + ")^{{({j})}}\\|".format(j = ordr2)
		if zpart == "": norm2 = "\\|" + wpart + "^{{({j})}}\\|".format(j = ordr2)
		if wpart == "": norm2 = "\\|" + zpart + "^{{({j})}}\\|".format(j = ordr2)
	
		if ordr2 == (0, 0): norm2 = "\\|" + wpart + zpart + "\\|"
		if zpart == "" and wpart == "": norm2 = ""
		
		
		pstr2 = format_exp(lbsg2)
		normind2 = "_{{W^{{{k},{p}}}}}".format(k = sblv2, p = pstr2)
		if lbsg2 == 2 and sblv2 > 0: normind2 = "_{{H^{k}}}".format(k = sblv2)
		if sblv2 == 0: normind2 = "_{{L^{{{p}}}}}".format(p = pstr2)
		if lbsg2 == math.inf: normind2 = "_{{W^{{{k},\\infty}}}}".format(k = sblv2)
		if lbsg2 == math.inf and sblv2 == 0: normind2 = "_{{L^\\infty}}"
		if norm2 == "" : normind2 = ""
	
		term2 = norm2 + normind2
	
	
		result = term1 + term2
		if fncs1 == "('1', (0, 0))*('1', (0, 0))": result = term2
		if fncs2 == "('1', (0, 0))*('1', (0, 0))": result = term1
		
		final += " + " + result
	
	return final
	

if __name__ == "__main__":

	
	#Testing
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (1, 0))*('v', (3, 2))", (0, 0), 1, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (2, 1))", (1, 2), 3, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (1, 0))*('v', (0, 0))", (0, 4), 2, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (1, 2))*('1', (0, 0))", (0, 0), 4, 6), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 0, 7)],
	         [("('u', (0, 0))*('1', (0, 0))", (0, 0), 6, 2), ("('v', (0, 0))*('1', (0, 0))", (7, 8), 7, 28)],
	         [("('u', (0, 0))*('1', (0, 0))", (0, 0), 0, 3), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 19, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (84, 2), 199, 67), ("('v', (0, 0))*('1', (0, 0))", (0, 3), 50, 2)],
	         [("('u', (0, 0))*('v', (1, 3))", (0, 0), 2, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 9))*('v', (0, 0))", (0, 0), 3, math.inf), ("('1', (0, 0))*('1', (1, 0))", (0, 0), 0, 0)]]
	
	print(sum_of_norms(norms))
	
	
	
	
	
	
	
	
	
