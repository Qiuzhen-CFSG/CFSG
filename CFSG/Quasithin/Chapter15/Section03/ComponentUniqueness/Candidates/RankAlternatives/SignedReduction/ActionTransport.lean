module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.Quotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.ActionLift

/-!
# Outer actors on the actual component quotient

An order-three element outside a full-three-rank component remains outer on
L/O₂(L). If its quotient action were conjugation by a quotient element, lift
that element to L. The resulting difference lies in the section-action kernel,
which is the ordinary centralizer because L is perfect and its two-core central.
The three-prime centralizer bound then contradicts the actor lying outside L.

We reuse the already published quotient-action homomorphism and its kernel
calculation. The theta generators construct the actor; no diagonal actor is
assumed. The final two transport lemmas turn membership in the actual GL₃ or
unitary conjugation image into the published diagonal-action predicates. Such
membership is still a concrete model obligation, not proved by this module.
For A.3.18 use `localQuotientEquiv` followed by the component-image equivalence.
All field orders and the unitary Frobenius are retained by that transport.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18
(printed pp.51--52), and the reductions in 15.3.37 and 15.3.43 (pp.1135, 1139).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction
variable {G H : Type*} [Group G] [Group H]

private theorem quotientAction_component {L : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* H) (l : L) :
    LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e
      ⟨l, L.le_normalizer l.property⟩ = MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) l)) := by
  ext z
  obtain ⟨x, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) z
  simp only [Function.comp_apply]
  rw [LinearCore.quotientAction_apply]
  change e (QuotientGroup.mk' (pCore 2 L) (l * x * l⁻¹)) =
    e (QuotientGroup.mk' (pCore 2 L) l) * e (QuotientGroup.mk' (pCore 2 L) x) *
      (e (QuotientGroup.mk' (pCore 2 L) l))⁻¹
  simp only [map_mul, map_inv]

private theorem outer_quotientAction {L : Subgroup G} [Group.IsPerfect L]
    (hcore : pCore 2 L ≤ center L) (e : (L ⧸ pCore 2 L) ≃* H)
    {y : G} (hy : y ∈ normalizer (L : Set G))
    (hno : ¬ ∃ l ∈ L, l⁻¹ * y ∈ Chapter4.sectionCentralizer L) :
    LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e ⟨y, hy⟩ ∉
      MulAut.innerSubgroup H := by
  rintro ⟨z, hz⟩
  obtain ⟨l, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) z
  simp only [Function.comp_apply] at hz
  let f := LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e
  let l' : normalizer (L : Set G) := ⟨l, L.le_normalizer l.property⟩
  let y' : normalizer (L : Set G) := ⟨y, hy⟩
  have hc : l'⁻¹ * y' ∈ f.ker := by
    change f (l'⁻¹ * y') = 1
    rw [map_mul, map_inv]
    have hl := quotientAction_component e l
    change f l' = _ at hl
    rw [hl, hz]
    exact inv_mul_cancel _
  rw [LinearCore.quotientAction_ker le_rfl e hcore] at hc
  apply hno
  refine ⟨l, l.property, ?_⟩
  rw [sectionCentralizer_eq_centralizer_of_perfect hcore]
  exact hc

variable [Finite G]

/-- An outside element of order three acts outerly on any model of L/O₂(L). -/
theorem quotient_action_outer {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    {y : G} (hyI : y ∈ I) (hy3 : orderOf y = 3) (hyL : y ∉ L)
    (hyN : y ∈ normalizer (L : Set G)) (e : (L ⧸ pCore 2 L) ≃* H) :
    LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e ⟨y, hyN⟩ ∉
      MulAut.innerSubgroup H := by
  let := hcomp.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)
  have hcore := (local_center_eq_twoCore hLI hcomp hodd).ge
  exact outer_quotientAction hcore e hyN
    (not_section_inner_of_order_three_outside hcore hLI hyI hy3 hyL
      (local_centralizer_three_coprime hLI hcomp hodd hrankL hrankI))

/-- The theta generators supply an outer actor on any coordinates for the actual quotient. -/
theorem exists_order_three_quotient_outer {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (e : (L ⧸ pCore 2 L) ≃* H) :
    ∃ y ∈ Yplus, ∃ hyN : y ∈ normalizer (L : Set G),
      y ∈ I ∧ orderOf y = 3 ∧ y ∉ L ∧
        LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e ⟨y, hyN⟩ ∉
          MulAut.innerSubgroup H := by
  obtain ⟨y, hy, hyMI, hy3, hyL⟩ := exists_order_three_outside_of_local hθ hnot
  have hYI : Yplus ≤ I := hθ ▸ (theta_le (M ⊓ I)).trans inf_le_right
  have hN := ComponentIntersection.normalizes_of_index_le_two hYI
    (hθ ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) hindex
  exact ⟨y, hy, hN hy, hyMI.2, hy3, hyL,
    quotient_action_outer hLI hcomp hodd hrankL hrankI hyMI.2 hy3 hyL (hN hy) e⟩

open scoped MatrixGroups

/-- Membership of the actual quotient action in the GL3 image gives the linear output.
For A.3.18, compose `localQuotientEquiv` with the component-image model equivalence. -/
theorem linear_diagonal_of_action_range {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    {y : G} (hyI : y ∈ I) (hy3 : orderOf y = 3) (hyL : y ∉ L)
    (hyN : y ∈ normalizer (L : Set G))
    {F : Type} [Field F] [Finite F] {q : ℕ} (hcard : Nat.card F = q)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (ha : LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e ⟨y, hyN⟩ ∈
      (Matrix.PSL3.OuterSolvable.linearConj F).range) :
    LinearDiagonalOnTwoQuotient L y q := by
  obtain ⟨d, hd⟩ := ha
  refine ⟨F, inferInstance, inferInstance, hcard, e,
    L.normalizerMonoidHom ⟨y, hyN⟩, d, (fun x => rfl), ?_, ?_⟩
  · rw [hd]
    exact quotient_action_outer hLI hcomp hodd hrankL hrankI hyI hy3 hyL hyN e
  · intro x
    rw [hd]
    exact (LinearCore.quotientAction_apply le_rfl e ⟨y, hyN⟩ x).symm

/-- The same transport uses the unitary field of order q squared and its q-Frobenius. -/
theorem unitary_diagonal_of_action_range {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    {y : G} (hyI : y ∈ I) (hy3 : orderOf y = 3) (hyL : y ∉ L)
    (hyN : y ∈ normalizer (L : Set G))
    {F : Type} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hfrob : ∀ x, J.conj x = x ^ q)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (ha : LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e ⟨y, hyN⟩ ∈
      J.unitaryConjHom.range) :
    UnitaryDiagonalOnTwoQuotient L y q := by
  obtain ⟨d, hd⟩ := ha
  refine ⟨F, inferInstance, inferInstance, J, hcard, hfrob, e,
    L.normalizerMonoidHom ⟨y, hyN⟩, d, (fun x => rfl), ?_, ?_⟩
  · rw [hd]
    exact quotient_action_outer hLI hcomp hodd hrankL hrankI hyI hy3 hyL hyN e
  · intro x
    rw [hd]
    exact (LinearCore.quotientAction_apply le_rfl e ⟨y, hyN⟩ x).symm

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction
