#!/usr/bin/python3.7

import random
import subprocess
import sys
import torch
import os

file_name = "FFN"

data_folder = "./"
yices = "yices-smt2"
DECPRECISION = 5
DECPRECISION_form = ".5f"

#   evaluate smt instance   ###########################################################################################
#######################################################################################################################

def evaluateSmt(smt_file_name):
    smt_out = subprocess.check_output([yices, data_folder+smt_file_name]).decode(sys.stdout.encoding)

    if smt_out[smt_out.find("phi")+4 : smt_out.find("phi")+6] != "(/":
        evaluation = int(smt_out[smt_out.find("phi")+4 : smt_out.find(")")])
    else:
        beginpos = smt_out.find("phi")+7
        endpos = beginpos+smt_out[beginpos:].find(" ")
        beginpos2 = endpos+1
        endpos2 = beginpos2+smt_out[beginpos2:].find(")")
        evaluation = int(smt_out[beginpos : endpos]) / int(smt_out[beginpos2 : endpos2])

    return evaluation

#   create smt instance   #############################################################################################
#######################################################################################################################

def createSmt(out_file_name, smt_file_name, instance_dimension, propositional_variables_values):
    formula = []
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
                    maxvar = max([maxvar,int(line[linepos_begin : linepos_end])])
                else:
                    clau = "(neg "+"X"+line[linepos_begin+1:linepos_end]+")"
                    maxvar = max([maxvar,int(line[linepos_begin+1:linepos_end])])

                while linepos_end+1 < len(line)-1:
                    linepos_begin = linepos_end+1
                    linepos_end = linepos_begin+line[linepos_begin:].find(" ")

                    if int(line[linepos_begin:linepos_end]) > 0:
                        clau = "(sdis "+clau+" X"+line[linepos_begin : linepos_end]+")"
                        maxvar = max([maxvar,int(line[linepos_begin : linepos_end])])
                    else:
                        clau = "(sdis "+clau+" (neg X"+line[linepos_begin+1 : linepos_end]+"))"
                        maxvar = max([maxvar,int(line[linepos_begin+1 : linepos_end])])

                formula.append(clau)

            elif ":: Negation" == line[line.find("::"):line.find("::")+11]:
                linepos_begin = line.find("::")+18
                linepos_end = len(line)-1

                formula.append("(neg "+formula[int(line[linepos_begin : linepos_end])-1]+")")

            elif ":: Implication" == line[line.find("::"):line.find("::")+14]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(impl "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")

            elif ":: Equivalence" == line[line.find("::"):line.find("::")+14]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(equiv "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")

            elif ":: Minimum" == line[line.find("::"):line.find("::")+10]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(min "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")

            elif ":: Maximum" == line[line.find("::"):line.find("::")+10]:
                linepos_begin = line.find("::")+18
                linepos_end = linepos_begin+line[linepos_begin:].find(" ")
                linepos_begin2 = linepos_end+1
                linepos_end2 = len(line)-1

                formula.append("(max "+formula[int(line[linepos_begin:linepos_end])-1]+" "+formula[int(line[linepos_begin2:linepos_end2])-1]+")")

        else:
            if formula:
                if not phi:
                    smt_aux.append("(assert (= phi "+formula[len(formula)-1]+"))")
                    phi = True
                else:
                    smt_aux.append("(assert (= "+formula[len(formula)-1]+" 1))")

                formula = []

    if formula:
        smt_aux.append("(assert (= "+formula[len(formula)-1]+" 1))")

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

    for var in range(1,maxvar+1):
        smt_file.write("(declare-fun X"+str(var)+" () Real)"+"\n")

    smt_file.write("\n")

    for var in range(instance_dimension+1,maxvar+1):
        smt_file.write("(assert (>= X"+str(var)+" 0))"+"\n")
        smt_file.write("(assert (<= X"+str(var)+" 1))"+"\n")

    smt_file.write("\n")

    for string in smt_aux:
        smt_file.write(string+"\n")

    smt_file.write("\n")

    for val in range(len(propositional_variables_values)):
        smt_file.write("(assert (= X"+str(val+1)+" "+format(propositional_variables_values[val], DECPRECISION_form)+"))"+"\n")

    smt_file.write("\n")
    smt_file.write("(check-sat)")
    smt_file.write("\n")
    smt_file.write("(get-value (phi))")

    smt_file.close()

#   main   ############################################################################################################
#######################################################################################################################

def test(x1, x2, x3, x4):
    global fail

    createSmt(file_name+".out", file_name+".smt", 4, [x1, x2, x3, x4])
    evalSmt = evaluateSmt(file_name+".smt")
    os.system("rm "+data_folder+file_name+".smt")

    output = nn(torch.as_tensor([x1, x2, x3, x4]).float())

    if abs(evalSmt - output.item()) < 10**-DECPRECISION:
        print("SUCCESS :-D || ", end='')
    else:
        print("FAIL!! :-( || ", end='')
        fail = 1

    print("x1: "+str(x1)+" | x2: "+str(x2)+" | x3: "+str(x3)+" | x4: "+str(x4)+" | PWL: "+str(evalSmt)+" | NN:  "+str(output.item()))

############

T = 1000
fail = 0

nn = torch.load(file_name+".nn")

for i in range(T):
    x1 = random.uniform(0,1)
    x2 = random.uniform(0,1)
    x3 = random.uniform(0,1)
    x4 = random.uniform(0,1)
    print(str(i+1)+" || ", end='')
    test(x1, x2, x3, x4)

print("\n", end='')
if fail:
    print("FAILED in at least one test :-(")
else:
    print("PASSED all tests! :-D")
