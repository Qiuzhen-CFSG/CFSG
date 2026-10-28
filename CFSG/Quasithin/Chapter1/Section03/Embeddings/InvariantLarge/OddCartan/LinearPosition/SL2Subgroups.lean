module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ResidualGeometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Transport

/-!
# Embedded SL₂ subgroups in the linear model

For q > 3, an embedded SL₂(q) is perfect and hence lies in the residual of
the centralizer of its central involution. The projective residual calculation
identifies that residual with SL₂(q), so equal orders give equality of the
actual ambient subgroups. Both cyclic factors in A.3.15(3) centralize this
involution, which therefore centralizes B.

This identifies the supplied subgroup without asserting its invariance.
Its position relative to the ambient Sylow center remains to be established.
The perfectness and equal-order argument is adapted from the parallel
`OddCartan.UnitaryPosition.SL2Subgroups` development.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of
1.3.4, printed pp.510–511.
-/

public section
open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- An actual SL₂(q) subgroup has a central involution in odd characteristic. -/
theorem sl2_exists_central_involution [Finite J] (K : Subgroup J)
    (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (e : K ≃* SL(2, ZMod q)) : ∃ z : K, z ∈ center K ∧ orderOf z = 2 := by
  have hc : Nat.card (center K) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    simpa only [GorensteinWalter.sl2ProjectiveProjection_ker] using
      GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod q) (by
        simpa only [Nat.card_eq_fintype_card, ZMod.card] using hq)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center K) 2 (by rw [hc])
  exact ⟨z, z.property, by simpa only [Subgroup.orderOf_coe] using hz⟩

/-- The embedded SL₂ is exactly the residual at its central involution. -/
theorem sl2_eq_involutionResidual [Finite J] (D K : Subgroup J) (hKD : K ≤ D)
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hmodel : ClassicalGroup.IsPSL D 3 q) (e : K ≃* SL(2, ZMod q))
    (z : K) (hzc : z ∈ center K) (hz : orderOf z = 2) :
    K = involutionResidual D z := by
  let : Group.IsPerfect (SL(2, ZMod q)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hlarge)
  let : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hle : K ≤ involutionResidual D z := by
    apply le_map_solvableResidual_of_isPerfect
    apply le_inf hKD
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun x : K => (x : J)) (mem_center_iff.mp hzc ⟨k, hk⟩))
  obtain ⟨er⟩ := involutionResidual_equiv hq hlarge hmodel (hKD z.property)
    (by simpa only [Subgroup.orderOf_coe] using hz)
  exact eq_of_le_of_card_ge hle (le_of_eq
    ((Nat.card_congr er.toEquiv).trans (Nat.card_congr e.toEquiv).symm))

/-- Both cyclic factors centralize the center of the supplied subgroup. -/
theorem CyclicDecomposition.le_centralizer_centerImage {B K : Subgroup J}
    (h : CyclicDecomposition B K) : B ≤ centralizer (centerImage K : Set J) := by
  rw [← h.generated]
  exact sup_le (inf_le_right.trans (OddCartan.le_centralizer_centerImage K))
    (inf_le_right.trans (centralizer_le (map_subtype_le _)))

/-- The supplied subgroup is based at an involution centralizing B.
This statement does not place that involution in the Sylow center. -/
theorem CaseThree.linear_involutionResidual [Finite J] {D B S K : Subgroup J}
    {q : ℕ} [Fact q.Prime] {ε : Sign}
    (h : CaseThree D B S K q .linear ε) (hlarge : 3 < q) :
    ∃ z ∈ D, orderOf z = 2 ∧ z ∈ centralizer (B : Set J) ∧
      K = involutionResidual D z := by
  obtain ⟨e⟩ := h.sl2
  obtain ⟨z, hzc, hz⟩ := sl2_exists_central_involution K q h.odd_characteristic e
  refine ⟨z, h.sl2_inside z.property, ?_, ?_, sl2_eq_involutionResidual D K h.sl2_inside q
    h.odd_characteristic hlarge h.model e z hzc hz⟩
  · simpa only [Subgroup.orderOf_coe] using hz
  · exact le_centralizer_iff.mp h.toCyclicDecomposition.le_centralizer_centerImage
      ⟨z, hzc, rfl⟩

/-- The SL₂ subgroup forces D to meet the ambient Sylow center in an involution. -/
theorem CaseThree.exists_central_involution [Finite J] {D B K : Subgroup J} {S : Sylow 2 J}
    {q : ℕ} [Fact q.Prime] {δ ε : Sign}
    [D.Normal] (h : CaseThree D B (S : Subgroup J) K q δ ε) :
    ∃ z ∈ D ⊓ centerImage (S : Subgroup J), orderOf z = 2 := by
  obtain ⟨e⟩ := h.sl2
  obtain ⟨z, _, hz⟩ := sl2_exists_central_involution K q h.odd_characteristic e
  have hd : 2 ∣ Nat.card D := (hz ▸ orderOf_dvd_natCard z).trans
    (Subgroup.card_dvd_of_le h.sl2_inside)
  exact exists_involution_mem_centerImage D S hd

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
