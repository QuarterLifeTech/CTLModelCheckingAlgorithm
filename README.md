# CTLModelCheckingAlgorithm
This repository contains an implementation of the computation tree logic model checking algorithm, SAT, defined on page 227, within the book Logic in Computer Science: Modelling and Reasoning About Systems by Michael Huth and Mark Ryan, second edition.

The algorithm is implemented in OCAML within the file "Thesis_First_Iteration.ml". 

Instructions:
1. Begin by downloading or cloning the repository.
2. Afterwards, if you do not have OCAML installed, please follow the instructions provided at https://ocaml.org/docs/install.html. 
3. Following the installation, depending on your operating system, open terminal or command line, type OCAML, and hit enter or return. This will open the OCAML interface. Afterword, type #use "Thesis_First_Iteration.ml" as this will load the .ml file.

Execution: 
To execute the sat algoirthm, simply type 'sat' and provide the method with three parameters, a model, labels and a CTL Formula. For example, typing 'sat models2 labels2 eu1' executes the sat algorithm with the mutual exclusion model example provided on page 226. You will find the variables models2, labels2 and eu1 on lines 123 to 125 in the file. Moreover, you will find other CTL formulas, models and labels defined on lines 128 and onward.
