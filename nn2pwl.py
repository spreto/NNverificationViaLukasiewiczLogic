#!/usr/bin/python3.7

import torch
import copy
import fractions
import random

nn_file_name = "FFN.nn"
pwl_file_name = "FFN.pwl"

nn = torch.load(nn_file_name)

w = nn.hidden_layer.weight.tolist()
b = nn.hidden_layer.bias.tolist()

prot = []

for i in range(len(b)):
    w[i].insert(0,b[i])
    prot.append(copy.deepcopy(w[i]))

w_out = nn.output_layer.weight.tolist()
b_out = nn.output_layer.bias.tolist()

w_out[0].insert(0,b_out[0])
w_out = w_out[0]

numLines = len(prot)

linearPieces = []

for i1 in range(2):
    for i2 in range(2):
        for i3 in range(2):
            for i4 in range(2):
                lP = []
                h = [i1, i2, i3, i4]
                for hindex in range(4):
                    if h[hindex] == 0:
                        lP.append("l "+str(hindex+1))
                    elif h[hindex] == 1:
                        lP.append("g "+str(hindex+1))

                newProt = 5*[0]
                newProt[0] = w_out[0]
                for hindex in range(4):
                    if h[hindex] == 1:
                        for x in range(5):
                            newProt[x] = newProt[x] + w[hindex][x]*w_out[hindex+1]
                prot.append(copy.deepcopy(newProt))
                newProt[0] = newProt[0] - 1
                prot.append(copy.deepcopy(newProt))

                for oindex in range(3):
                    lP2 = copy.deepcopy(lP)
                    if oindex == 0:
                        lP2.append("l "+str(len(prot)-1))
                        linearPieces.append([[0, 0, 0, 0, 0], lP2])
                    elif oindex == 1:
                        lP2.append("g "+str(len(prot)-1))
                        lP2.append("l "+str(len(prot)))
                        linearPieces.append([copy.deepcopy(prot[-2]), lP2])
                    elif oindex == 2:
                        lP2.append("g "+str(len(prot)))
                        linearPieces.append([[1, 0, 0, 0, 0], lP2])

############

pwl_file = open(pwl_file_name, "w")
pwl_file.write("pwl\n")

for bound in prot:
    pwl_file.write("b ")
    for i in range(5):
        auxBound = round(bound[i],6)
        bound[i] = auxBound
        pwl_file.write(str(bound[i]))
        if i != 4:
            pwl_file.write(" ")
        else:
            pwl_file.write("\n")

for lin in linearPieces:
    pwl_file.write("p ")
    for i in range(5):
        auxFrac = fractions.Fraction.from_float(round(lin[0][i],6)).limit_denominator(10**6)
        lin[0][i] = auxFrac
        pwl_file.write(str(lin[0][i].numerator)+" "+str(lin[0][i].denominator))
        if i != 4:
            pwl_file.write(" ")
        else:
            pwl_file.write("\n")
    for i in range(len(lin[1])):
        pwl_file.write(lin[1][i])
        pwl_file.write("\n")

pwl_file.close()

############

def test(x1, x2, x3, x4):
    global fail
    auxBool = 0
    ind = -1

    while not auxBool:
        auxBool = 1
        ind = ind + 1
        for bound in linearPieces[ind][1]:
            dtm = prot[int(bound[2:len(bound)])-1][0] + prot[int(bound[2:len(bound)])-1][1]*x1 + prot[int(bound[2:len(bound)])-1][2]*x2 + \
                prot[int(bound[2:len(bound)])-1][3]*x3 + prot[int(bound[2:len(bound)])-1][4]*x4
            if dtm > 0 and bound[0] == 'l':
                auxBool = 0
            elif dtm < 0 and bound[0] == 'g':
                auxBool = 0

    dtm = linearPieces[ind][0][0] + linearPieces[ind][0][1]*x1 + linearPieces[ind][0][2]*x2 + linearPieces[ind][0][3]*x3 + \
        linearPieces[ind][0][4]*x4
    output = nn(torch.as_tensor([x1, x2, x3, x4]).float())

    if abs(dtm - output.item()) < 10**-5:
        print("SUCCESS :-D || ", end='')
    else:
        print("FAIL!! :-( || ", end='')
        fail = 1

    print("x1: "+str(x1)+" | x2: "+str(x2)+" | x3: "+str(x3)+" | x4: "+str(x4)+" | PWL: "+str(dtm)+" | NN:  "+str(output.item()))

############

T = 100000
fail = 0

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
