import math
import actions
import numpy as np
from collections import deque
from ast import literal_eval as make_tuple

#Just converting the norm tuples into a latex-type string for display purposes - nothing interesting here


class Norm:
	def __init__(self, tup):
		self.tup = tup
		
		self.fncs = tup[0]
		self.ordr = tup[1]
		self.sblv = tup[2]
		self.lbsg = tup[3]


def sum_of_norms(norms):

	norm = norms[0]
	tup1 = Norm(norm[0]); tup2 = Norm(norm[1])
	fncs1 = tup1.fncs; fncs2 = tup2.fncs
	ordr1 = tup1.ordr; ordr2 = tup2.ordr
	lbsg1 = tup1.lbsg; lbsg2 = tup2.lbsg
	sblv1 = tup1.sblv; sblv2 = tup2.sblv
	
	splits1 = tup1.fncs.split("*")
	FuncData11 = make_tuple(splits1[0]); FuncData12 = make_tuple(splits1[1])
	ord11 = FuncData11[1]; ord12 = FuncData12[1]
	
	splits2 = tup2.fncs.split("*")
	FuncData21 = make_tuple(splits2[0]); FuncData22 = make_tuple(splits2[1])
	ord21 = FuncData21[1]; ord22 = FuncData22[1]
	
	upart = "{u}".format(u = FuncData11[0]) + "^{{({ord11})}}".format(ord11 = ord11)
	if ord11 == 0: upart = "{u}".format(u = FuncData11[0])
	if ord11 == 1: upart = "{u}'".format(u = FuncData11[0])
	if ord11 == 2: upart = "{u}''".format(u = FuncData11[0])
	if FuncData11[0] == '1': upart = ""
	
	vpart = "{v}".format(v = FuncData12[0]) + "^{{({ord12})}}".format(ord12 = ord12)
	if ord12 == 0: vpart = "{v}".format(v = FuncData12[0])
	if ord12 == 1: vpart = "{v}'".format(v = FuncData12[0])
	if ord12 == 2: vpart = "{v}''".format(v = FuncData12[0])
	if FuncData12[0] == '1': vpart = ""
	
	norm1 = "\\|(" + upart + vpart + ")^{{({j})}}\\|".format(j = ordr1)
	if vpart == "": norm1 = "\\|" + upart + "^{{({j})}}\\|".format(j = ordr1)
	if upart == "": norm1 = "\\|" + vpart + "^{{({j})}}\\|".format(j = ordr1)
	
	if ordr1 == 0: norm1 = "\\|" + upart + vpart + "\\|"
	
	if ordr1 == 1: 
		norm1 = "\\|(" + upart + vpart + ")'\\|"
		if vpart == "": norm1 = "\\|" + upart + "'\\|"
		if upart == "": norm1 = "\\|" + vpart + "'\\|"
	
	if ordr1 == 2: 
		norm1 = "\\|(" + upart + vpart + ")''\\|"
		if vpart == "": norm1 = "\\|" + upart + "''\\|"
		if upart == "": norm1 = "\\|" + vpart + "''\\|"
		
	normind1 = "_{{W^{{{k},{p}}}}}".format(k = sblv1, p = lbsg1)
	if lbsg1 == 2 and sblv1 > 0: normind1 = "_{{H^{k}}}".format(k = sblv1)
	if sblv1 == 0: normind1 = "_{{L^{p}}}".format(p = lbsg1)
	if lbsg1 == math.inf: normind1 = "_{{W^{{{k},oo}}}}".format(k = sblv1)
	if lbsg1 == math.inf and sblv1 == 0: normind1 = "_{{L^oo}}"
	
	term1 = norm1 + normind1



	wpart = "{w}".format(w = FuncData21[0]) + "^{{({ord21})}}".format(ord21 = ord21)
	if ord21 == 0: wpart = "{w}".format(w = FuncData21[0])
	if ord21 == 1: wpart = "{w}'".format(w = FuncData21[0])
	if ord21 == 2: wpart = "{w}''".format(w = FuncData21[0])
	if FuncData21[0] == '1': wpart = ""
	
	zpart = "{z}".format(z = FuncData22[0]) + "^{{({ord22})}}".format(ord22 = ord22)
	if ord22 == 0: zpart = "{z}".format(z = FuncData22[0])
	if ord22 == 1: zpart = "{z}'".format(z = FuncData22[0])
	if ord22 == 2: zpart = "{z}''".format(z = FuncData22[0])
	if FuncData22[0] == '1': zpart = ""
	
	norm2 = "\\|(" + wpart + zpart + ")^{{({j})}}\\|".format(j = ordr2)
	if zpart == "": norm2 = "\\|" + wpart + "^{{({j})}}\\|".format(j = ordr2)
	if wpart == "": norm2 = "\\|" + zpart + "^{{({j})}}\\|".format(j = ordr2)
	
	if ordr2 == 0: norm2 = "\\|" + wpart + zpart + "\\|"
		
	if ordr2 == 1: 
		norm2 = "\\|(" + wpart + zpart + ")'\\|"
		if zpart == "": norm2 = "\\|" + wpart + "'\\|"
		if wpart == "": norm2 = "\\|" + zpart + "'\\|"
		
	if ordr2 == 2: 
		norm2 = "\\|(" + wpart + zpart + ")''\\|"
		if zpart == "": norm2 = "\\|" + wpart + "''\\|"
		if wpart == "": norm2 = "\\|" + zpart + "''\\|"
		
	normind2 = "_{{W^{{{k},{p}}}}}".format(k = sblv2, p = lbsg2)
	if lbsg2 == 2 and sblv2 > 0: normind2 = "_{{H^{k}}}".format(k = sblv2)
	if sblv2 == 0: normind2 = "_{{L^{p}}}".format(p = lbsg2)
	if lbsg2 == math.inf: normind2 = "_{{W^{{{k},oo}}}}".format(k = sblv2)
	if lbsg2 == math.inf and sblv2 == 0: normind2 = "_{{L^oo}}"
	
	term2 = norm2 + normind2
	
	
	result = term1 + term2
	if fncs1 == "('1', 0)*('1', 0)": result = term2
	if fncs2 == "('1', 0)*('1', 0)": result = term1
	final = result
	
	for i in range(1, len(norms)):
	
		norm = norms[i]
		tup1 = Norm(norm[0]); tup2 = Norm(norm[1])
		fncs1 = tup1.fncs; fncs2 = tup2.fncs
		ordr1 = tup1.ordr; ordr2 = tup2.ordr
		lbsg1 = tup1.lbsg; lbsg2 = tup2.lbsg
		sblv1 = tup1.sblv; sblv2 = tup2.sblv
	
		splits1 = tup1.fncs.split("*")
		FuncData11 = make_tuple(splits1[0]); FuncData12 = make_tuple(splits1[1])
		ord11 = FuncData11[1]; ord12 = FuncData12[1]
	
		splits2 = tup2.fncs.split("*")
		FuncData21 = make_tuple(splits2[0]); FuncData22 = make_tuple(splits2[1])
		ord21 = FuncData21[1]; ord22 = FuncData22[1]
	
		upart = "{u}".format(u = FuncData11[0]) + "^{{({ord11})}}".format(ord11 = ord11)
		if ord11 == 0: upart = "{u}".format(u = FuncData11[0])
		if ord11 == 1: upart = "{u}'".format(u = FuncData11[0])
		if ord11 == 2: upart = "{u}''".format(u = FuncData11[0])
		if FuncData11[0] == '1': upart = ""
	
		vpart = "{v}".format(v = FuncData12[0]) + "^{{({ord12})}}".format(ord12 = ord12)
		if ord12 == 0: vpart = "{v}".format(v = FuncData12[0])
		if ord12 == 1: vpart = "{v}'".format(v = FuncData12[0])
		if ord12 == 2: vpart = "{v}''".format(v = FuncData12[0])
		if FuncData12[0] == '1': vpart = ""
	
		norm1 = "\\|(" + upart + vpart + ")^{{({j})}}\\|".format(j = ordr1)
		if vpart == "": norm1 = "\\|" + upart + "^{{({j})}}\\|".format(j = ordr1)
		if upart == "": norm1 = "\\|" + vpart + "^{{({j})}}\\|".format(j = ordr1)
	
		if ordr1 == 0: norm1 = "\\|" + upart + vpart + "\\|"
	
		if ordr1 == 1: 
			norm1 = "\\|(" + upart + vpart + ")'\\|"
			if vpart == "": norm1 = "\\|" + upart + "'\\|"
			if upart == "": norm1 = "\\|" + vpart + "'\\|"
	
		if ordr1 == 2: 
			norm1 = "\\|(" + upart + vpart + ")''\\|"
			if vpart == "": norm1 = "\\|" + upart + "''\\|"
			if upart == "": norm1 = "\\|" + vpart + "''\\|"
		
		normind1 = "_{{W^{{{k},{p}}}}}".format(k = sblv1, p = lbsg1)
		if lbsg1 == 2 and sblv1 > 0: normind1 = "_{{H^{k}}}".format(k = sblv1)
		if sblv1 == 0: normind1 = "_{{L^{p}}}".format(p = lbsg1)
		if lbsg1 == math.inf: normind1 = "_{{W^{{{k},oo}}}}".format(k = sblv1)
		if lbsg1 == math.inf and sblv1 == 0: normind1 = "_{{L^oo}}"
	
		term1 = norm1 + normind1



		wpart = "{w}".format(w = FuncData21[0]) + "^{{({ord21})}}".format(ord21 = ord21)
		if ord21 == 0: wpart = "{w}".format(w = FuncData21[0])
		if ord21 == 1: wpart = "{w}'".format(w = FuncData21[0])
		if ord21 == 2: wpart = "{w}''".format(w = FuncData21[0])
		if FuncData21[0] == '1': wpart = ""
	
		zpart = "{z}".format(z = FuncData22[0]) + "^{{({ord22})}}".format(ord22 = ord22)
		if ord22 == 0: zpart = "{z}".format(z = FuncData22[0])
		if ord22 == 1: zpart = "{z}'".format(z = FuncData22[0])
		if ord22 == 2: zpart = "{z}''".format(z = FuncData22[0])
		if FuncData22[0] == '1': zpart = ""
		
		norm2 = "\\|(" + wpart + zpart + ")^{{({j})}}\\|".format(j = ordr2)
		if zpart == "": norm2 = "\\|" + wpart + "^{{({j})}}\\|".format(j = ordr2)
		if wpart == "": norm2 = "\\|" + zpart + "^{{({j})}}\\|".format(j = ordr2)
	
		if ordr2 == 0: norm2 = "\\|" + wpart + zpart + "\\|"
		
		if ordr2 == 1: 
			norm2 = "\\|(" + wpart + zpart + ")'\\|"
			if zpart == "": norm2 = "\\|" + wpart + "'\\|"
			if wpart == "": norm2 = "\\|" + zpart + "'\\|"
		
		if ordr2 == 2: 
			norm2 = "\\|(" + wpart + zpart + ")''\\|"
			if zpart == "": norm2 = "\\|" + wpart + "''\\|"
			if wpart == "": norm2 = "\\|" + zpart + "''\\|"
		
		normind2 = "_{{W^{{{k},{p}}}}}".format(k = sblv2, p = lbsg2)
		if lbsg2 == 2 and sblv2 > 0: normind2 = "_{{H^{k}}}".format(k = sblv2)
		if sblv2 == 0: normind2 = "_{{L^{p}}}".format(p = lbsg2)
		if lbsg2 == math.inf: normind2 = "_{{W^{{{k},oo}}}}".format(k = sblv2)
		if lbsg2 == math.inf and sblv2 == 0: normind2 = "_{{L^oo}}"
	
		term2 = norm2 + normind2
	
	
		result = term1 + term2
		if fncs1 == "('1', 0)*('1', 0)": result = term2
		if fncs2 == "('1', 0)*('1', 0)": result = term1
		
		final += " + " + result
	
	return final
