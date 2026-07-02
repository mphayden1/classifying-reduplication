# classifying-reduplication
This is the companion code to the paper [_Algebraic Classification of Reduplicative Processes_](https://aclanthology.org/2026.scil-main.42/)<sup>1</sup> presented at the Society for Computation in Linguistics 2026 meeting, co-located with the The 64th Annual Meeting of the Association for Computational Linguistics (ACL) in San Diego. 

This study was conducted on RedTyp<sup>2</sup>, a database of finite-state models for reduplication available at https://github.com/jhdeov/RedTyp.

This repository contains the following:
* A folder labeled __FST__ extracted from the RedTyp database of reduplicative transducers
* `classifier.py` is a script for computing and classifying the transition semigroup of a two-way deterministic finite-state transducer
* `classify_redtyp.py` runs the classifier script on the transducers in __FST__
* A file `morphemeIDs.txt` which contains the ID tags for each transducer, indexed by line number.
* A file `results.txt` which is the output of the `classify_redtyp.py`

An up-to-date Python installation is required to run the scripts. To replicate the experiment, simply run the following in the terminal:
```
python3 classify_redtyp.py
```
Additionally, `classifier.py` can be run in the interpreter on an arbitrary two-way transducer as long as the transition function is given in the correct format.
```
import classifier
classifier.transitions =  [('state_p', 'in_symb', 'state_q', 'out_symb', '+/-1'), ...]
classifier.main()
```

<sup>1</sup>Matthew Hayden. 2026. Algebraic Classification of Reduplicative Processes. In Proceedings of the Society for Computation in Linguistics 2026, pages 447–459, San Diego, CA. Association for Computational Linguistics.

<sup>2</sup>Hossep Dolatian and Jeffrey Heinz. 2019. RedTyp: A Database of Reduplication with Computational Models. In Proceedings of the Society for Computation in Linguistics (SCiL) 2019, pages 8–18.
