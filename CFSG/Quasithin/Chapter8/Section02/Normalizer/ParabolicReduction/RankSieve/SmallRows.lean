module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.LocalActions
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.PrimeOrders

/-!
# The L₃(4) and M₂₂ rows of the rank sieve

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of Lemma 8.2.9, printed pp.720–721
(PDF pp.737–738).

`LocalActions` proves the three- and five-rank deductions with the actual A₅
quotient marking. From the two local commutator actions in N_G(U)/U it obtains
B ≤ O₂(H) in the L₃(4) row and the literal order-two/order-four intersection
alternatives in the M₂₂ row. It derives the relative index from the dimension
of V/B, without assuming the intersection equality.

`PrimeOrders` controls odd product orders from the actual pair quotient
models and supplies prime residual order, hence all ResidualLift conclusions,
for the actual PSL₂(2) and cyclic-five alternatives.

The full branch theorem remains to be assembled. Still required are the
source 7.3.4/Table 7.2.1 parameter specialization, instantiation of the local
module commutators, exclusion of the four-group case, n(H)=1, recognition of
the relevant pair-family members, and inspection of every E.2.2/B.6.8 model
with its parameter and automizer restrictions. The Aut(L₃(2)) and PSL₂(31)
exceptions must retain their residual markings for the separate chief-section
argument. None of these unproved steps is replaced by a narrowed list here.
-/
