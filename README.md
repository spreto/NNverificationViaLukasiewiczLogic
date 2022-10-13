# Neural network verification via Łukasiewicz logic

This repository contains the files related to an experiment to formally verify a neural network via Łukasiewicz Infinitely-valued Logic.

- *model.py* and *train.py* have the routines for training the neural network.

- *nn2pwl.py* has the routine to translate from the neural network in *FFN.nn* to the file *FFN.pwl*, which codifies a rational McNaughton function in regional format and is the input for [pwl2limodsat](http://github.com/spreto/pwl2limodsat), which translates from *FFN.pwl* to *FFN.out*, which has a representation modulo satisfiability of the neural network into the Łukasiewicz Infinitely-valued Logic.

- *outTest.py* has the routine to test the representation in *FFN.out* with random values.

- *reachability.py* has the routine to verify the reachability of the neural network.

- *robustness.py* has the routine to verify the robustness of the neural network.

- The verification outputs were moved to folders *precision_5/* and *precision_10/*.
