
# Theorem Prover

An automated theorem prover based on Hilbert system for  propositional logic.

Usage:
			```     > python3 hilbert.py ```

When prompted, enter the formula in the specified format.
Only formulas constructed with ⊥ (bottom) and ⊃ (implication) connectives are allowed as input.
Output is a sequence of derivation steps, if the given formula is provable.

Sample run:
```
> python3 hilbert.py

Please write the theorem. (use | for derivation sign, > for implication and - for bottom)

p > q, q > r | p > r

Using deduction theorem and proving q > r,p > q,p | r

Derivation steps

0 q > r ...... Assumption 0

1 p > q ...... Assumption 1

2 p ...... Assumption 2

3 q ...... MP 1,2

4 r ...... MP 0,3
```


