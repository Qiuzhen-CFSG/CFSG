module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDefs
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportInvolutions
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportOrders
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportPermutation

/-!
# Small-support involutions and odd factors

This module assembles Aschbacher--Smith, *The Classification of Quasithin
Groups*, D.2.11–12, printed pp.183–184, for a finite faithful action on an
elementary abelian two-group. Binary ranks are expressed by the equivalent
support cardinalities, independently of the action-ratio definitions.

The exported statements corresponding to the source clauses are:

* D.2.11(1): `invertedOddElement_order_three_of_involution_card_two`.
* D.2.11(2): `invertedOddElement_order_three_or_five_of_involution_card_four`.
* D.2.11(3): `invertedOddElement_full_support`, including both centralizer
  conclusions and equality of the actual displacement subgroups.
* The action facts for the D.2.11(4) bridge to `Q(G,V)`:
  `cyclicInvolution_quadratic` and `cyclicInvolution_card_eq_fixed_mul_commutator`.
  Membership in the chapter's action-ratio family is left to that interface;
  no such family or membership is assumed here.
* D.2.12(1–2): `smallSupport_decomposition`, with independence, commutation,
  and generation for the canonical factors and their actual supports.
* D.2.12(3): `smallSupportFactors_involution_alternative`.
* D.2.12(4): `smallSupportFactors_normalized_of_displacement_card`.
* D.2.12(5): `smallSupportFactors_normalized_or_single_transposition`.

Coprime splitting and inversion give the square-support formula, and the
small binary linear groups give the order restrictions. Local support
rigidity and the nilpotent normalizer argument give the canonical direct
product and direct sum. Independence then bounds the displacement needed to
move a factor, proving the normalization and unique-transposition alternatives.
All premises of the conditional decomposition and permutation helpers are
discharged by these exported results, including for an empty factor family.
-/
