# CSCI561 Project 1
## Authors: Clayton Kramp, Hunter Johnson, Matthew Baldin
## Files Contained:
### project-1.lisp
This is the main file containing the main methods for the project. The main functions we implemented are:
#### regex->nfa
This takes in an input a regex and outputs an nfa constructed with make-nfa.  This follows McNaughton-Yamada-Thompson Algorithm.
#### nfa->dfa
This function will use the subset construction algorithm to convert the input nfa to a dfa.  The function calls eps-closure and move-eps-closure as well.
#### dfa->minimize
This function runs the Brzozowski's Algorithm.  The function calls reverse-dfa and nfa-\>dfa to minimize the input dfa.
### FA\_Wumpus.lisp
This file contains the make-fa function for transitions, start, and accept states to create a dot file corresponding the the DES of the Wumpus.
### FA\_Human.lisp
This file contains the make-fa function for transitions, start, and accept states to create a dot file corresponding the the DES of the Human.
### Readme
This
