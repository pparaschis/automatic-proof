import math
import actions2D as actions
import numpy as np
from SumOfNorms2D import sum_of_norms
from ast import literal_eval
from collections import deque
import time
import psutil
import subprocess
import os

# This script builds a BFS proof tree for 2D product/Sobolev norm bounds and
# exports both terminal output and a LaTeX document with per-step action labels.
# Needs some improvement in the script format, but the result's would not change




#Memory-based stopping criterion - can be skipped if RAM is large enough
#for skipping, comment out "import psutil" and the two following lines
proc = psutil.Process()
THRESHOLD = 3 * 1024**3  # 3 GB



class TreeNode:

    #Initialize the node with data and an empty list of children
    def __init__(self, data):
        self.data = data
        self.children = []
        self.parents = None
        self.nchildren = 0
        self.ancestors = [self]
        self.isleaf = False
        # Label describing which operation generated this node from its parent.
        self.transition = "Initial bound"

    #Add a child node and update its ancestors
    def add_child(self, child):
        self.children.append(child)
        self.nchildren += 1
        child.ancestors = [anc for anc in self.ancestors] + child.ancestors
        child.parents = self

        
class Norm:
    def __init__(self, tup):

        #Data of the norm-tuple - stored as a class for convenience
        self.tup = tup
        
        self.fncs = tup[0]
        self.ordr = tup[1]
        self.sblv = tup[2]
        self.lbsg = tup[3]


def _wrap_sum_expression(expr, terms_per_line = 3):
    # Soft-wrap "a + b + c + ..." strings to keep generated TeX readable.
    terms = expr.split(" + ")
    if len(terms) <= terms_per_line:
        return [expr]
    return [" + ".join(terms[i:i + terms_per_line]) for i in range(0, len(terms), terms_per_line)]


def write_proofs_tex(proofs, tex_path, title = "Tree Norm Proofs"):
    # Write proof chains to LaTeX and annotate each inequality step with its generating action.
    def latex_escape(text):
        repl = {
            "\\": "\\textbackslash{}",
            "&": "\\&",
            "%": "\\%",
            "$": "\\$",
            "#": "\\#",
            "_": "\\_",
            "{": "\\{",
            "}": "\\}",
            "~": "\\textasciitilde{}",
            "^": "\\textasciicircum{}",
        }
        out = str(text)
        for k, v in repl.items():
            out = out.replace(k, v)
        return out

    def emit_wrapped_math(lines, expr, prefix = "", terms_per_line = 3, indent = "\\quad ", keep_open = True, note = None):
        wrapped = _wrap_sum_expression(expr, terms_per_line = terms_per_line)
        end = " \\\\" if (keep_open or len(wrapped) > 1) else ""
        note_tex = ""
        if note:
            # Keep the explanation compact to avoid overflow on long lines.
            note_tex = " \\quad\\text{\\scriptsize(" + latex_escape(note) + ")}"
        lines.append("&" + prefix + wrapped[0] + note_tex + end)
        for cont in wrapped[1:]:
            lines.append("&" + indent + "+ " + cont + " \\\\")

    lines = []
    # TeX preamble tuned for long multiline proofs.
    lines.append("\\documentclass[11pt]{article}")
    lines.append("\\usepackage{amsmath,amssymb,mathtools}")
    lines.append("\\usepackage[margin=1in]{geometry}")
    lines.append("\\begin{document}")
    lines.append("\\allowdisplaybreaks")
    lines.append("\\setlength{\\jot}{0.6em}")
    lines.append("\\small")
    lines.append("\\section*{" + title + "}")

    if proofs == []:
        lines.append("No completed proof was found.")
    else:
        # Each proof is one ancestor chain; each step has expression + transition note.
        for i, proof in enumerate(proofs, start = 1):
            lines.append("\\subsection*{Proof " + str(i) + "}")
            lines.append("\\begin{align*}")
            # First line is the initial bound; no transition note attached.
            emit_wrapped_math(lines, proof[0]["expr"], prefix = "", terms_per_line = 3, indent = "\\quad ", keep_open = True, note = None)
            for j in range(1, len(proof)):
                is_last = (j == len(proof) - 1)
                emit_wrapped_math(
                    lines,
                    proof[j]["expr"],
                    prefix = "\\lesssim ",
                    terms_per_line = 3,
                    indent = "\\quad ",
                    keep_open = not is_last,
                    note = proof[j]["transition"]
                )
            lines.append("\\end{align*}")

    lines.append("\\end{document}")

    with open(tex_path, "w") as f:
        f.write("\n".join(lines) + "\n")


def compile_tex_to_pdf(tex_path):
    # Compile the generated TeX in-place and return either PDF path or failure reason.
    tex_dir = os.path.dirname(tex_path)
    tex_file = os.path.basename(tex_path)
    pdf_path = os.path.splitext(tex_path)[0] + ".pdf"
    try:
        subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_file],
            cwd = tex_dir,
            stdout = subprocess.DEVNULL,
            stderr = subprocess.DEVNULL,
            check = True
        )
        return True, pdf_path
    except FileNotFoundError:
        return False, "pdflatex not found"
    except subprocess.CalledProcessError:
        return False, "pdflatex compilation failed"


def build_tree(root, pinit_u, pmax_u, pinit_v, pmax_v, step, kmax, pmax, lmax, qmax, depth, prune_mode_lvl, prune_mode_leaf):

    '''
	Inputs:

	root: Root node of the tree - initial norms to be bounded
	pmax_u: Maximum p-value for the Holder exponents w.r.t. u
    pinit_u: Initial p-value for the Holder exponents w.r.t. u
	pmax_v: Maximum p-value for the Holder exponents w.r.t. v
    pinit_v: Initial p-value for the Holder exponents w.r.t. v
	step: Step size for the p-values
	kmax: Maximal regularity in u
	lmax: Maximal regularity in v
	depth: Maximum depth of the tree

	Builds a tree of norm bounds using breadth-first search and prunes branches that reach maximal regularity.
    '''

	
    # Initial exponent grid used by Holder branches (per-term ranges are refined later).
    prange_u = np.arange(pinit_u, pmax_u + step, step) #Range of p-values for Holder exponents
    
    queue = deque([root]) #Queue for breadth-first search
    levels = [[root]]
    visited = set() #Set of visited norm-sets to avoid duplicates
    leafnodes = set() #Set of leaf nodes

    totalnnodes = 1
    proofs = []
	
    # Standard BFS over proof states.
    while queue:
        parent = queue.popleft()
		
		
        current_depth = len(parent.ancestors) - 1 #Calculate current depth
        lvl = current_depth + 1
        if current_depth == depth: continue #Stop if max depth reached
			
        # Frontiers and terminal flags for current state.
        MakeLeafReg, MakeLeafHolder, KHmax, LHmax, Kmax, Lmax = actions.CheckRegularity(parent.data, kmax, pmax, lmax, qmax) #Check regularity

        if MakeLeafHolder: #if all terms are Holder-splitted

            
            normnew = [[("('u', (0, 0))*('1', (0, 0))", (0, 0), kp[0], kp[1]), \
                        ("('v', (0, 0))*('1', (0, 0))", (0, 0), lq[0], lq[1])] for kp in KHmax for lq in LHmax]
			
            normnew_tuple = tuple(tuple(item) for item in normnew) #convert to tuple of tuples for set operations 
            if parent.isleaf == False: # and normnew_tuple not in visited:
				
				
                # Compare candidate terminal state against existing leaves before adding it.
                LowScore = False
                for leaf in leafnodes: 
                    Ku = [(norma[0][2], norma[0][3]) for norma in leaf.data]; Ku = list(set(Ku))
                    Lv = [(norma[1][2], norma[1][3]) for norma in leaf.data]; Lv = list(set(Lv))
					            	
                    ustronger, vstronger = actions.compare(KHmax, LHmax, Ku, Lv, mode = prune_mode_leaf)

                    if ustronger and vstronger: LowScore = True
                    if LowScore: break

                if LowScore: visited.add(normnew_tuple)

                
                if not LowScore:
                    if normnew_tuple not in visited:
                        visited.add(normnew_tuple)
                        normleaf = TreeNode(normnew)
                        normleaf.transition = "Terminalization: all terms Holder-splitted"
                        parent.add_child(normleaf)
                        queue.append(normleaf) #add to queue for further processing
                        normleaf.isleaf = True #mark as leaf
                        leafnodes.add(normleaf) #add to leaf nodes set
                        totalnnodes += 1

                        if len(levels) <= lvl: levels += [[]]
                        levels[lvl].append(normleaf)
                    else: #this one covers the case where the sum of norms contains just one term
                        parent_tuple = tuple(tuple(item) for item in parent.data)
                        visited.add(parent_tuple)
                        parent.isleaf = True #mark as leaf
                        leafnodes.add(parent) #add to leaf nodes set  

                       
						
		
		
        if parent.isleaf:

	    	#Print the proof for the leaf node in latex format
            # Serialize both formulas and transition labels along the ancestor path.
            proof_steps = [{"expr": sum_of_norms(ancestor.data), "transition": ancestor.transition} for ancestor in parent.ancestors]
            proofs.append(proof_steps)
		
			
            # Emit the full chain to terminal, including transition reasons.
            print(" ")
            print("Proof complete!")
            print("{anc}".format(anc = proof_steps[0]["expr"]))
            for i in range(1, len(proof_steps)):
                print("    \\lesssim {ancestor}    [{why}]".format(ancestor = proof_steps[i]["expr"], why = proof_steps[i]["transition"]))
			
            print(" ")
			
			
            continue 

        else:

            #If the node is not in a terminal state, then compare it once more with the leafs,
            #in case new weaker ones where created on the same level after this one
            #if so, then don't expand it further
            LowScore = False

            # Prune current parent if dominated by a same-level node.
            # `safe` mode requires full frontier domination; `aggressive` is existential.
            #compare with the nodes of the same depth
            if len(levels) <= lvl: levels += [[]]
            Kpar = KHmax + Kmax; Lpar = LHmax + Lmax
            
            for node in levels[lvl]: 
                if node in parent.ancestors: continue
                
                #Get maximum regularities of both
                KHlevel, LHlevel, Klevel, Llevel = actions.GetMaxReg(node.data)
                
                Klvl = KHlevel + Klevel; Llvl = LHlevel + Llevel
                u_low, v_low = actions.compare(Kpar, Lpar, Klvl, Llvl, mode = prune_mode_lvl)

                #if the current node has stronger regularity than the other one,
                #then it has a lower score
                if u_low and v_low: 
                    LowScore = True
                    break

            # Also prune if already dominated by any completed leaf state.
            for leaf in leafnodes: 
                if LowScore: break
                
                KHleaf = [(comp[0][2], comp[0][3]) for comp in leaf.data]
                LHleaf = [(comp[1][2], comp[1][3]) for comp in leaf.data]
                
                u_low, v_low = actions.compare(Kpar, Lpar, KHleaf, LHleaf, mode = prune_mode_leaf)

                if u_low and v_low: LowScore = True

            if LowScore: 

                #if the node has a low score, delete it
                #also, delete the ancestors leading only to this node
                ancestors_rev = parent.ancestors
                ancestors_rev.reverse()
                for anc in ancestors_rev:
                    if anc.nchildren > 0: break
                    anc.parents.children.remove(anc)
                    anc.parents.nchildren -= 1
                    totalnnodes -= 1
                continue

	
        # Expand children by applying all admissible operations to each term.
        for i in range(len(parent.data)): #iterate over all terms in the sum of norms
	
            tup0 = Norm(parent.data[i][0])
	
            splits0 = tup0.fncs.split("*") #split the function string to get individual functions
            FuncData01 = literal_eval(splits0[0]); FuncData02 = literal_eval(splits0[1])
            ord01 = FuncData01[1]; ord02 = FuncData02[1] #orders of the individual functions
			
            #If Holder's inequality has not yet been applied to this norm
            #and if the norm is not yet at maximal regularity
            if FuncData02[0] != '1' and abs(tup0.ordr[0] + tup0.ordr[1] + tup0.sblv) == 0 \
            	and parent.isleaf == False and MakeLeafReg == False: 
                prange_u = np.arange(max(pinit_u, tup0.lbsg), max(pmax_u, tup0.lbsg) + step, step)
                prange_v = np.arange(max(pinit_v, tup0.lbsg), max(pmax_v, tup0.lbsg) + step, step)
						
				# Apply Holder on the u-side factor across the allowed exponent range.
                for p in prange_u:
                    normnew = actions.Holder(parent.data, i, 0, p)
                    normnew = actions.eliminate(normnew) #eliminate duplicates
                    normnew = actions.absorb_weaker(normnew) #absorb the weaker norms by stronger ones
                    normnew = sorted(normnew) #sort for consistency
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)


                    LowScore = False

                    # Candidate-level prune against same-level nodes.
                    #compare with the nodes of the same depth
                    if len(levels) <= lvl: levels += [[]]
                    
                    KHnew, LHnew, Knew, Lnew = actions.GetMaxReg(normnew)
                    
                    Knode = KHnew + Knew; Lnode = LHnew + Lnew
                    for node in levels[lvl]: 
                        if node in parent.ancestors: continue
                
				        #Get maximum regularities of both
                        KHlevel, LHlevel, Klevel, Llevel = actions.GetMaxReg(node.data)
				        
                        Klvl = KHlevel + Klevel; Llvl = LHlevel + Llevel
                        u_low, v_low = actions.compare(Knode, Lnode, Klvl, Llvl, mode = prune_mode_lvl)

				        #if the current node has stronger regularity than the other one,
				        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    # Candidate-level prune against leaves.
                    for leaf in leafnodes: 
                        if LowScore: break
				        
                        KHleaf = [(comp[0][2], comp[0][3]) for comp in leaf.data]
                        LHleaf = [(comp[1][2], comp[1][3]) for comp in leaf.data]
				        
                        u_low, v_low = actions.compare(Knode, Lnode, KHleaf, LHleaf, mode = prune_mode_leaf)

                        if u_low and v_low: LowScore = True

                            


                    if normnew_tuple not in visited: #if not yet visited
                        visited.add(normnew_tuple) #mark as visited

                        # Keep only non-dominated candidates.
                        #if it isn't stronger than either the leaf or the same-depth nodes , 
                        #then create child;
                        #it will be compared further when it is dequed, in case 
                        #weaker (more promising) nodes are created afterwards
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            # Holder split applied on u-side of term i.
                            normnode.transition = "Action: Holder, term {term}, function u, target exponent p={p}".format(term = i + 1, p = p)
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1

                # Repeat Holder branching on the v-side factor.
                for p in prange_v:
                    normnew = actions.Holder(parent.data, i, 1, p)
                    normnew = actions.eliminate(normnew) #eliminate duplicates
                    normnew = actions.absorb_weaker(normnew) #absorb the weaker norms by stronger ones
                    normnew = sorted(normnew) #sort for consistency
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)

                    LowScore = False

                    #compare with the nodes of the same depth
                    if len(levels) <= lvl: levels += [[]]
                    
                    KHnew, LHnew, Knew, Lnew = actions.GetMaxReg(normnew)
                    
                    Knode = KHnew + Knew; Lnode = LHnew + Lnew
                    for node in levels[lvl]: 
                        if node in parent.ancestors: continue
                
				        #Get maximum regularities of both
                        KHlevel, LHlevel, Klevel, Llevel = actions.GetMaxReg(node.data)
				        
                        Klvl = KHlevel + Klevel; Llvl = LHlevel + Llevel
                        u_low, v_low = actions.compare(Knode, Lnode, Klvl, Llvl, mode = prune_mode_lvl)

				        #if the current node has stronger regularity than the other one,
				        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    for leaf in leafnodes: 
                        if LowScore: break
				        
                        KHleaf = [(comp[0][2], comp[0][3]) for comp in leaf.data]
                        LHleaf = [(comp[1][2], comp[1][3]) for comp in leaf.data]
				        
                        u_low, v_low = actions.compare(Knode, Lnode, KHleaf, LHleaf, mode = prune_mode_leaf)

                        if u_low and v_low: LowScore = True


                            

                    if normnew_tuple not in visited: #if not yet visited
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            # Holder split applied on v-side of term i.
                            normnode.transition = "Action: Holder, term {term}, function v, target exponent q={p}".format(term = i + 1, p = p)
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1
					
            # Structural operations act on either factor (j in {0,1}) of term i.
            for j in range(2): #iterate over the two functions in the norm

                tup = Norm(parent.data[i][j])
			
                splits = tup.fncs.split("*") #split as above
                FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
                ord1 = FuncData1[1]; ord2 = FuncData2[1]
				
                #If the total derivative order is positive
                #and the term is not yet Holdered
                #and the norm is not yet at maximal regularity
                # Leibniz product expansion for derivative-bearing terms.
                if tup.ordr[0] + tup.ordr[1] != 0 and tup.fncs != "('1', (0, 0))*('1', (0, 0))" \
					and FuncData02[0] != '1' and parent.isleaf == False and MakeLeafReg == False:
                    normnew = actions.prod(parent.data, i, j) #product rule
                    normnew = actions.eliminate(normnew)
                    normnew = actions.absorb_weaker(normnew)
                    normnew = sorted(normnew)
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)
                    
                    
                    LowScore = False

                    #compare with the nodes of the same depth
                    if len(levels) <= lvl: levels += [[]]
                    
                    KHnew, LHnew, Knew, Lnew = actions.GetMaxReg(normnew)
                    
                    Knode = KHnew + Knew; Lnode = LHnew + Lnew
                    for node in levels[lvl]: 
                        if node in parent.ancestors: continue
                
				        #Get maximum regularities of both
                        KHlevel, LHlevel, Klevel, Llevel = actions.GetMaxReg(node.data)
				        
                        Klvl = KHlevel + Klevel; Llvl = LHlevel + Llevel
                        u_low, v_low = actions.compare(Knode, Lnode, Klvl, Llvl, mode = prune_mode_lvl)

				        #if the current node has stronger regularity than the other one,
				        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    for leaf in leafnodes: 
                        if LowScore: break
				        
                        KHleaf = [(comp[0][2], comp[0][3]) for comp in leaf.data]
                        LHleaf = [(comp[1][2], comp[1][3]) for comp in leaf.data]
				        
                        u_low, v_low = actions.compare(Knode, Lnode, KHleaf, LHleaf, mode = prune_mode_leaf)

                        if u_low and v_low: LowScore = True

                            

                    if normnew_tuple not in visited: 
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            # Leibniz rule applied to selected factor j of term i.
                            normnode.transition = "Action: Product rule, term {term}, factor {fac}".format(term = i + 1, fac = j + 1)
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1
				
				# expansion of a Sobolev norm into seminorm contributions.
                if tup.sblv != 0 and tup.fncs != "('1', (0, 0))*('1', (0, 0))" and FuncData02[0] != '1' \
				 	and parent.isleaf == False and MakeLeafReg == False:
                    normnew = actions.expand(parent.data, i, j) #expand Sobolev norm to sum of seminorms
                    normnew = actions.eliminate(normnew)
                    normnew = actions.absorb_weaker(normnew)
                    normnew = sorted(normnew)
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)

                    LowScore = False

                    #compare with the nodes of the same depth
                    if len(levels) <= lvl: levels += [[]]
                    
                    KHnew, LHnew, Knew, Lnew = actions.GetMaxReg(normnew)
                    
                    Knode = KHnew + Knew; Lnode = LHnew + Lnew
                    for node in levels[lvl]: 
                        if node in parent.ancestors: continue
                
				        #Get maximum regularities of both
                        KHlevel, LHlevel, Klevel, Llevel = actions.GetMaxReg(node.data)
				        
                        Klvl = KHlevel + Klevel; Llvl = LHlevel + Llevel
                        u_low, v_low = actions.compare(Knode, Lnode, Klvl, Llvl, mode = prune_mode_lvl)

				        #if the current node has stronger regularity than the other one,
				        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    for leaf in leafnodes: 
                        if LowScore: break
				        
                        KHleaf = [(comp[0][2], comp[0][3]) for comp in leaf.data]
                        LHleaf = [(comp[1][2], comp[1][3]) for comp in leaf.data]
				        
                        u_low, v_low = actions.compare(Knode, Lnode, KHleaf, LHleaf, mode = prune_mode_leaf)

                        if u_low and v_low: LowScore = True

                            

                    if normnew_tuple not in visited: 
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            # Sobolev norm expanded into seminorm contributions.
                            normnode.transition = "Action: Sobolev expansion, term {term}, factor {fac}".format(term = i + 1, fac = j + 1)
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1

                # Rellich-Kondrachov embedding branch.
                if tup.fncs != "('1', (0, 0))*('1', (0, 0))" and FuncData02[0] != '1' \
				    and parent.isleaf == False and MakeLeafReg == False:
                    normnew = actions.embed(parent.data, i, j) #apply Sobolev embedding
                    normnew = actions.eliminate(normnew)
                    normnew = actions.absorb_weaker(normnew)
                    normnew = sorted(normnew)
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)

                    LowScore = False

                    #compare with the nodes of the same depth
                    if len(levels) <= lvl: levels += [[]]
                    
                    KHnew, LHnew, Knew, Lnew = actions.GetMaxReg(normnew)
                    
                    Knode = KHnew + Knew; Lnode = LHnew + Lnew
                    for node in levels[lvl]: 
                        if node in parent.ancestors: continue
                
				        #Get maximum regularities of both
                        KHlevel, LHlevel, Klevel, Llevel = actions.GetMaxReg(node.data)
				        
                        Klvl = KHlevel + Klevel; Llvl = LHlevel + Llevel
                        u_low, v_low = actions.compare(Knode, Lnode, Klvl, Llvl, mode = prune_mode_lvl)

				        #if the current node has stronger regularity than the other one,
				        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    for leaf in leafnodes: 
                        if LowScore: break

                        KHleaf = [(comp[0][2], comp[0][3]) for comp in leaf.data]
                        LHleaf = [(comp[1][2], comp[1][3]) for comp in leaf.data]

                        u_low, v_low = actions.compare(Knode, Lnode, KHleaf, LHleaf, mode = prune_mode_leaf)

                        if u_low and v_low: LowScore = True

                            

                    if normnew_tuple not in visited: 
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            # Rellich-Kondrachov embedding on selected factor.
                            normnode.transition = "Action: Sobolev embedding, term {term}, factor {fac}".format(term = i + 1, fac = j + 1)
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1
                            

        #If no children were added and there are nonsplitted terms, 
        #prune the branch and remove ancestors  only leading to this node,
        #so that you won't have any useless leaf nodes
        ancestors_rev = parent.ancestors
        ancestors_rev.reverse()
        for anc in ancestors_rev:
            if anc.nchildren > 0: break
            anc.parents.children.remove(anc)
            anc.parents.nchildren -= 1
            totalnnodes -= 1

        #for skipping the memory-based stopping criterion,
        #comment out the three following lines as well
        if proc.memory_info().rss >= THRESHOLD:
            print("Memory threshold reached; stopping loop.")
            break

    print("Total number of nodes:", totalnnodes)
    return proofs, totalnnodes
    
		
# --- Script entry configuration ---
# Example problem: find upper bounds for \|uv\|_{W^{k,q}} with chosen k,q.
funcs = "('u', (0, 0))*('v', (0, 0))"
norms = [[(funcs, (0, 0), 1, 1.5), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)]]

tup_init = Norm(norms[0][0])
pinit_u = tup_init.lbsg; pmax_u = 5
pinit_v = tup_init.lbsg; pmax_v = 5


norms = sorted(norms)

kmax = math.inf; lmax = math.inf; step = 1
#kmax = 3; lmax = 3; step = 1



start_time = time.time()
root = TreeNode(norms); depth = math.inf
prune_mode_lvl = "safe" # options: "safe", "aggressive"
prune_mode_leaf = "aggressive"
proofs, totalnnodes = build_tree(root, pinit_u, pmax_u, pinit_v, pmax_v, step, kmax, math.inf, lmax, math.inf, depth, prune_mode_lvl, prune_mode_leaf)
end_time = time.time()

script_dir = os.path.dirname(os.path.abspath(__file__))
tex_path = os.path.join(script_dir, "automatic_proofs2D.tex")
write_proofs_tex(proofs, tex_path, title = "Tree Norm Proofs With Step Explanations (" + prune_mode_lvl + " pruning compared to the same level and " \
																	+ prune_mode_leaf + " pruning compared to terminal nodes)")
pdf_ok, pdf_info = compile_tex_to_pdf(tex_path)

print(" ")
print("Total computation time: {time} seconds".format(time = end_time - start_time))
print("Proofs written to: {path}".format(path = tex_path))
if pdf_ok:
    print("PDF written to: {path}".format(path = pdf_info))
else:
    print("PDF not generated: {msg}".format(msg = pdf_info))
print(" ")
		
		
				
