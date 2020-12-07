#!/usr/bin/python3.7

import subprocess
import sys
import os
import math

data_folder = "./"
yices = "yices-smt2"

file_name = "FFN"

nn_dim = 4
delta = 0.04

pi = [17, 32]
# pi = [53, 100]
# pi = [52, 100]
# pi = [51, 100]
# pi = [1, 2]

#   create smt instance   #############################################################################################
#######################################################################################################################

def createSmt(out_file_name, smt_file_name, instance_dimension, epsilon, pi):
    alpha = epsilon[0]
    beta = epsilon[1]
    ahh = pi[0]
    behh = pi[1]

    formula = []
    _formula = []
    maxvar = instance_dimension
    phi = False
    smt_aux = []

    out_file = open(data_folder+out_file_name, "r")

    for line in out_file:
        if "Unit" == line[0:4]:
            if ":: Clause" == line[line.find("::"):line.find("::")+9]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")

                if int(line[linepos_begin:linepos_end]) > 0:
                    clau = "X"+line[linepos_begin : linepos_end]
                    _clau = "_X"+line[linepos_begin : linepos_end]
                    maxvar = max([maxvar,int(line[linepos_begin : linepos_end])])
                else:
                    clau = "(neg "+"X"+line[linepos_begin+1:linepos_end]+")"
                    _clau = "(neg "+"_X"+line[linepos_begin+1:linepos_end]+")"
                    maxvar = max([maxvar,int(line[linepos_begin+1:linepos_end])])

                while linepos_end+1 < len(line)-1:
                    linepos_begin = linepos_end+1
                    linepos_end = linepos_begin+line[linepos_begin:].find(" ")

                    if int(line[linepos_begin:linepos_end]) > 0:
                        clau = "(sdis "+clau+" X"+line[linepos_begin : linepos_end]+")"
                        _clau = "(sdis "+_clau+" _X"+line[linepos_begin : linepos_end]+")"
                        maxvar = max([maxvar,int(line[linepos_begin : linepos_end])])
                    else:
                        clau = "(sdis "+clau+" (neg X"+line[linepos_begin+1 : linepos_end]+"))"
                        _clau = "(sdis "+_clau+" (neg _X"+line[linepos_begin+1 : linepos_end]+"))"
                        maxvar = max([maxvar,int(line[linepos_begin+1 : linepos_end])])

                formula.append(clau)
                _formula.append(_clau)

            elif ":: Negation" == line[line.find("::"):line.find("::")+11]:
                linepos_begin = line.find("::")+18
                linepos_end = len(line)-1

                formula.append("(neg "+formula[int(line[linepos_begin : linepos_end])-1]+")")
                _formula.append("(neg "+_formula[int(line[linepos_begin : linepos_end])-1]+")")

            elif ":: Implication" == line[line.find("::"):line.find("::")+14]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(impl "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")
                _formula.append("(impl "+_formula[int(line[linepos_begin:linepos_end])-1]+" "+_formula[int(line[linepos_begin2:linepos_end2])-1]+")")

            elif ":: Equivalence" == line[line.find("::"):line.find("::")+14]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(equiv "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")
                _formula.append("(equiv "+_formula[int(line[linepos_begin:linepos_end])-1]+" "+_formula[int(line[linepos_begin2:linepos_end2])-1]+")")

            elif ":: Minimum" == line[line.find("::"):line.find("::")+10]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(min "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")
                _formula.append("(min "+_formula[int(line[linepos_begin:linepos_end])-1]+" "+_formula[int(line[linepos_begin2:linepos_end2])-1]+")")

            elif ":: Maximum" == line[line.find("::"):line.find("::")+10]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(max "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")
                _formula.append("(max "+_formula[int(line[linepos_begin:linepos_end])-1]+" "+_formula[int(line[linepos_begin2:linepos_end2])-1]+")")

        else:
            if formula:
                if not phi:
                    smt_aux.append("(assert (= phi "+formula[len(formula)-1]+"))")
                    smt_aux.append("(assert (= _phi "+_formula[len(_formula)-1]+"))")
                    phi = True
                else:
                    smt_aux.append("(assert (= "+formula[len(formula)-1]+" 1))")
                    smt_aux.append("(assert (= "+_formula[len(_formula)-1]+" 1))")

                formula = []
                _formula = []

    if formula:
        smt_aux.append("(assert (= "+formula[len(formula)-1]+" 1))")
        smt_aux.append("(assert (= "+_formula[len(_formula)-1]+" 1))")

    out_file.close()

    smt_file = open(data_folder+smt_file_name, "w")

    smt_file.write("(set-logic QF_LRA)"+"\n")
    smt_file.write("(define-fun min ((x Real) (y Real)) Real(ite (> x y) y x))"+"\n")
    smt_file.write("(define-fun max ((x Real) (y Real)) Real(ite (> x y) x y))"+"\n")
    smt_file.write("(define-fun sdis ((x Real) (y Real)) Real(min 1 (+ x y)))"+"\n")
    smt_file.write("(define-fun scon ((x Real) (y Real)) Real(max 0 (- (+ x y) 1)))"+"\n")
    smt_file.write("(define-fun wdis ((x Real) (y Real)) Real(max x y))"+"\n")
    smt_file.write("(define-fun wcon ((x Real) (y Real)) Real(min y x))"+"\n")
    smt_file.write("(define-fun neg ((x Real)) Real(- 1 x))"+"\n")
    smt_file.write("(define-fun impl ((x Real) (y Real)) Real(min 1 (- (+ 1 y) x)))"+"\n")
    smt_file.write("(define-fun equiv ((x Real) (y Real)) Real(- 1 (max (- x y) (- y x))))"+"\n")
    smt_file.write("\n")
    smt_file.write("(declare-fun phi () Real)"+"\n")
    smt_file.write("(declare-fun _phi () Real)"+"\n")

    for var in range(1,maxvar+1):
        smt_file.write("(declare-fun X"+str(var)+" () Real)"+"\n")
        smt_file.write("(declare-fun _X"+str(var)+" () Real)"+"\n")

    smt_file.write("\n")

    for var in range(1,maxvar+1):
        smt_file.write("(assert (>= X"+str(var)+" 0))"+"\n")
        smt_file.write("(assert (<= X"+str(var)+" 1))"+"\n")
        smt_file.write("(assert (>= _X"+str(var)+" 0))"+"\n")
        smt_file.write("(assert (<= _X"+str(var)+" 1))"+"\n")

    smt_file.write("\n")

    for string in smt_aux:
        smt_file.write(string+"\n")

    smt_file.write("\n")

    smt_file.write("(declare-fun half () Real)"+"\n")
    smt_file.write("(assert (>= half 0))"+"\n")
    smt_file.write("(assert (<= half 1))"+"\n")
    smt_file.write("(assert (= (equiv half (neg half)) 1))"+"\n")

    smt_file.write("\n")

    if beta == 1 or behh == 1:
        smt_file.write("(declare-fun one () Real)"+"\n")
        smt_file.write("(assert (>= one 0))"+"\n")
        smt_file.write("(assert (<= one 1))"+"\n")
        smt_file.write("\n")

    smt_file.write("(declare-fun beta () Real)"+"\n")
    smt_file.write("(assert (>= beta 0))"+"\n")
    smt_file.write("(assert (<= beta 1))"+"\n")
    if beta > 1:
        betaAux = "beta"
        for i in range(beta-2):
            betaAux = "(sdis beta "+betaAux+")"
        smt_file.write("(assert (= (equiv beta (neg "+betaAux+")) 1))"+"\n")
    else:
        smt_file.write("(assert (= (equiv beta (sdis one (neg one))) 1))"+"\n")

    smt_file.write("\n")

    smt_file.write("(declare-fun b () Real)"+"\n")
    smt_file.write("(assert (>= b 0))"+"\n")
    smt_file.write("(assert (<= b 1))"+"\n")
    if behh > 1:
        behhAux = "b"
        for i in range(behh-2):
            behhAux = "(sdis b "+behhAux+")"
        smt_file.write("(assert (= (equiv b (neg "+behhAux+")) 1))"+"\n")
    else:
        smt_file.write("(assert (= (equiv b (sdis one (neg one))) 1))"+"\n")

    smt_file.write("\n")

    alphaAux = "beta"
    for i in range(alpha-1):
        alphaAux = "(sdis beta "+alphaAux+")"

    for i in range(1, instance_dimension+1):
        smt_file.write("(declare-fun P"+str(i)+" () Real)"+"\n")
        smt_file.write("(assert (>= P"+str(i)+" 0))"+"\n")
        smt_file.write("(assert (<= P"+str(i)+" 1))"+"\n")
        smt_file.write("(assert (= (impl P"+str(i)+" "+alphaAux+") 1))"+"\n")
        smt_file.write("(assert (= (wdis (equiv _X"+str(i)+" (sdis X"+str(i)+" P"+str(i)+")) (equiv _X"+str(i)+" (neg (impl X"+str(i)+" P"+str(i)+")))) 1))"+"\n")

    smt_file.write("\n")

    ahhAux = "b"
    for i in range(ahh-1):
        ahhAux = "(sdis b "+ahhAux+")"

    smt_file.write("(assert (= (impl "+ahhAux+" phi) 1))"+"\n")

    smt_file.write("\n")

    smt_file.write("(assert (< (impl half _phi) 1))")

    smt_file.write("\n")

    smt_file.write("(check-sat)")

#######
#    smt_file.write("(get-value (X1))")
#    smt_file.write("(get-value (P1))")
#    smt_file.write("(get-value (_X1))")
#    smt_file.write("(get-value (phi))")
#    smt_file.write("(get-value (_phi))")
#######

    smt_file.close()

#   main   ############################################################################################################
#######################################################################################################################

print("Iteration: 0/k")
createSmt(data_folder+file_name+".out", data_folder+file_name+".smt", nn_dim, [1, 1], pi)
smt_out = subprocess.check_output([yices, data_folder+file_name+".smt"]).decode(sys.stdout.encoding)
os.system("rm "+data_folder+file_name+".smt")

if smt_out[0] == "u":
    v_min = [1, 1]
else:
    k = math.ceil(abs(math.log2(delta)))
    v_min = [0, 1]

    for j in range(1,k+1):
        print("Iteration: "+str(j)+"/"+str(k))
        v_max = v_min
        while v_max[1] != 2**j:
            v_max = [2*v_max[0], 2*v_max[1]]
        v_max[0] = v_max[0] + 1

        createSmt(data_folder+file_name+".out", data_folder+file_name+".smt", nn_dim, v_max, pi)
        smt_out = subprocess.check_output([yices, data_folder+file_name+".smt"]).decode(sys.stdout.encoding)
        os.system("rm "+data_folder+file_name+".smt")

        if smt_out[0] == "u":
            v_min = v_max

print("pi    = "+str(pi[0])+"/"+str(pi[1]))
print("delta = "+str(delta))
print("E     = "+str(v_min[0])+"/"+str(v_min[1]))

result_file = open(data_folder+file_name+"_robust_"+str(pi[0])+"_"+str(pi[1])+".txt", "w")
result_file.write("pi    = "+str(pi[0])+"/"+str(pi[1])+"\n")
result_file.write("delta = "+str(delta)+"\n")
result_file.write("E     = "+str(v_min[0])+"/"+str(v_min[1])+"\n")
result_file.close()
