module

public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import Theory.GroupTheory.TINormalizerControl
public import CFSG.Quasithin.Chapter12.Section03.WeightFour

/-!
# The rank bridge in the `A₇` case

The last sentence in the printed proof of Aschbacher--Smith, Lemma 12.3.9,
does not follow from the preceding intersection statement: the displayed
weight-four plane is properly contained in the binary `[7,3,4]` simplex code.
The correct local interface has two parts.  The weight-two and weight-six
cases are handled by the centralizers from Lemmas 12.3.6 and 12.3.8 and the
TI normalizer calculation.  A rank-three all-weight-four subspace is a real
remaining case and needs one additional source input controlling its
centralizer (or an equivalent weak-closure statement).

This file proves the reusable implication once that precise extra input is
supplied.  Thus it does not silently promote the false maximality assertion
to a theorem.  The parent Section 12.3 assembly must instantiate
`simplex_centralizer_le` from the missing group argument; the concrete
counterexample to the old linear assertion is recorded in `WeightFour.lean`.

Source: Aschbacher--Smith, §12.3, printed pp. 807--812 (PDF pp. 824--829),
especially Lemmas 12.3.3--8 and Definition E.3.3 (printed p. 231).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.Chapter12.Section03

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The exact local data needed for the repaired rank argument.

`weight` is the weight in the natural six-dimensional `A₇` module.  The
`low_codim_split` field is the elementary binary calculation: a subgroup of
corank at most three either contains a weight-two or weight-six vector, or is
an all-weight-four rank-three (simplex) case.  The latter is deliberately
represented by a separate predicate, since the plane in the printed proof is
not maximal.  `simplex_centralizer_le` is the one additional genuine source
obligation left by the correction.
-/
structure RankRepairHypotheses (G : Type u) [Group G] [Finite G] where
  V : Subgroup G
  M : Subgroup G
  elementary : IsElementaryAbelian 2 (V : Type u)
  nontrivial : V ≠ ⊥
  /-- `N_G(V) ≤ M`, as in the Section 12.3 setup. -/
  normalizer_le : normalizer (V : Set G) ≤ M
  /-- The TI condition for `V` inside `M` (12.2.6). -/
  ti : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
    V.map (MulAut.conj g).toMonoidHom = V
  /-- The natural module's six-dimensional rank, in quotient form. -/
  rank_eq_six : subgroupCorank V (⊥ : Subgroup G) = 6
  weight : G → ℕ
  /-- The all-weight-four branch.  This includes the simplex code case. -/
  simplex : Subgroup G → Prop
  /-- Binary weight classification for every subgroup of corank at most three. -/
  low_codim_split : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U ≤ 3 →
    (∃ v ∈ U, v ≠ 1 ∧ (weight v = 2 ∨ weight v = 6)) ∨ simplex U
  /-- Lemmas 12.3.6 and 12.3.8, for weights six and two. -/
  weight_centralizer_le : ∀ v : G, v ∈ V → v ≠ 1 →
    (weight v = 2 ∨ weight v = 6) → centralizer ({v} : Set G) ≤ M
  /--
  The repaired simplex-code input.  It is intentionally explicit: the
  concrete `[7,3,4]` code shows that it cannot be obtained from the weight
  restriction alone.  A parent proof may replace this by any equivalent weak
  closure statement for simplex subspaces.
  -/
  simplex_centralizer_le : ∀ U : Subgroup G, U ≤ V → simplex U →
    centralizer (U : Set G) ≤ M

namespace RankRepairHypotheses

variable (H : RankRepairHypotheses (G := G))

include H

theorem centralizer_le_M_of_weight {v : G} (hv : v ∈ H.V) (hv1 : v ≠ 1)
    (hw : H.weight v = 2 ∨ H.weight v = 6) :
    centralizer ({v} : Set G) ≤ H.M :=
  H.weight_centralizer_le v hv hv1 hw

theorem nontrivial_of_corank_le_three {U : Subgroup G}
    (hcorank : subgroupCorank H.V U ≤ 3) : U ≠ ⊥ := by
  intro hbot
  have hsix := H.rank_eq_six
  rw [hbot] at hcorank
  omega

private theorem centralizer_le_M_of_low_codim {U : Subgroup G}
    (hU : U ≤ H.V) (hcorank : subgroupCorank H.V U ≤ 3) :
    centralizer (U : Set G) ≤ H.M := by
  rcases H.low_codim_split U hU hcorank with hweight | hsimplex
  · obtain ⟨v, hvU, hv1, hw⟩ := hweight
    exact (centralizer_le (Set.singleton_subset_iff.mpr hvU)).trans
      (H.centralizer_le_M_of_weight (hU hvU) hv1 hw)
  · exact H.simplex_centralizer_le U hU hsimplex

/--
Every subspace of corank at most three has its ambient centralizer in
`N_G(V)`.  The weight-two/six branch uses the existing TI normalizer theorem;
the all-weight-four branch uses the explicit simplex centralizer input.
-/
public theorem centralizer_le_normalizer_of_corank_le_three
    {U : Subgroup G} (hU : U ≤ H.V)
    (hcorank : subgroupCorank H.V U ≤ 3) :
    centralizer (U : Set G) ≤ normalizer (H.V : Set G) := by
  let _ := H.elementary
  have hUne : U ≠ ⊥ := H.nontrivial_of_corank_le_three hcorank
  have hM := H.centralizer_le_M_of_low_codim hU hcorank
  have hTI := Subgroup.inf_centralizer_le_normalizer_of_trivial_intersections
    H.ti hUne hU
  exact (le_inf hM le_rfl).trans hTI

/--
The repaired E.3.3 consequence: no escaping-centralizer subgroup of `V` has
binary corank below four.  In the source notation this is `r(G,V) ≥ 4`, with
`globalR` the formal realization of `r`.
-/
public theorem globalR_ge_four : (4 : ℕ∞) ≤ globalR H.V := by
  let _ := H.elementary
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hU, hescape⟩
  have hnat : 4 ≤ subgroupCorank H.V U := by
    by_contra hnot
    have hcorank : subgroupCorank H.V U ≤ 3 := by
      have : subgroupCorank H.V U < 4 := Nat.lt_of_not_ge hnot
      omega
    exact hescape (H.centralizer_le_normalizer_of_corank_le_three hU hcorank)
  exact ENat.natCast_le_natCast.mpr hnat

/-- Source-numbered alias for the repaired part (2) of Lemma 12.3.9. -/
public theorem lemma_12_3_9_2 : (4 : ℕ∞) ≤ globalR H.V :=
  H.globalR_ge_four

/-- A natural-number presentation of `globalR_ge_four`. -/
public theorem four_le_globalR_toNat (hR : globalR H.V ≠ ⊤) :
    4 ≤ (globalR H.V).toNat := by
  have h := H.globalR_ge_four
  exact ENat.toNat_le_toNat h hR

end RankRepairHypotheses

end CFSG.Quasithin.Chapter12.Section03

end
