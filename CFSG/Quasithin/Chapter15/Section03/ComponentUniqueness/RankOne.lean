module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Quotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Configuration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroup

/-!
# The remaining S₃ quotient in Section 15.3

This boundary assembles the work toward Aschbacher--Smith 15.3.43,
combined manuscript (1 March 2004), printed pp.1139--1140.

`Basic` proves the three-rank consequence of (a), clause (c), the
nontrivial component action, and the minimality step `I = LS` conditional
on `Y₊ ≤ L`. `Quotient` constructs `I/C_I(L)` with relative normality,
transports its Sylow subgroup, and proves its normalizer and properness
statements. It identifies `L⁺` with `L/Z(L)` by a canonical equivalence.
`FourGroup` proves that the original `V₂` embeds faithfully in this
quotient and retains its normality and full commutator action.
The remaining local properties are an explicit output contract.

The deductions (a), (b), (d), component containment, the remaining clauses
of (e), and the model exclusions still have to be assembled. No theorem
asserting 15.3.43 is exported until these premises have been discharged.
-/
