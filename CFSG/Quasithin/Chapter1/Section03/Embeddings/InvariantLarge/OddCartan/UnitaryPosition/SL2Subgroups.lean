module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Residual

/-!
# Embedded SL₂ subgroups in the unitary model

An embedded SL₂(q), for q > 3, is perfect and has a central involution.
It lies in that involution's centralizer residual. The projective unitary
residual calculation gives the same order, proving equality of the actual
ambient subgroups, rather than just an abstract isomorphism.

For the cyclic factorization of A.3.15(3), both factors centralize the center
of the supplied SL₂. Consequently its central involution centralizes B.
Locating this involution relative to the ambient Sylow center is a separate
remaining geometric step.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of 1.3.4,
printed pp.510–511.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Both cyclic factors centralize the center of the supplied subgroup. -/
theorem cyclicDecomposition_le_centralizer_centerImage {B K : Subgroup G}
    (h : CyclicDecomposition B K) : B ≤ centralizer (centerImage K : Set G) := by
  rw [← h.generated]
  exact sup_le (inf_le_right.trans (le_centralizer_centerImage K))
    (inf_le_right.trans (centralizer_le (map_subtype_le _)))

/-- An actual SL₂(q) subgroup has a central involution when q is odd. -/
theorem sl2_exists_central_involution (K : Subgroup G)
    (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    ∃ z : K, z ∈ center K ∧ orderOf z = 2 := by
  have hc : Nat.card (center K) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    simpa only [GorensteinWalter.sl2ProjectiveProjection_ker] using
      GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod q) (by
        simpa only [Nat.card_eq_fintype_card, ZMod.card] using hq)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center K) 2 (by rw [hc])
  exact ⟨z, z.property, by simpa only [Subgroup.orderOf_coe] using hz⟩

/-- The embedded SL₂ is exactly the residual at its central involution. -/
theorem sl2_eq_involutionResidual (D K : Subgroup G) (hKD : K ≤ D)
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hmodel : ClassicalGroup.IsPSU D 3 q)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (z : K) (hzc : z ∈ center K) (hz : orderOf z = 2) :
    K = involutionResidual D ⟨z, hKD z.property⟩ := by
  let w : D := ⟨z, hKD z.property⟩
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hlarge)
  let : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let ek := subgroupOfEquivOfLe hKD
  let : Group.IsPerfect (K.subgroupOf D) :=
    Group.IsPerfect.ofSurjective (f := ek.symm.toMonoidHom) ek.symm.surjective
  have hKC : K.subgroupOf D ≤ centralizer ({w} : Set D) := by
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact congrArg (fun x : K => (x : G)) (mem_center_iff.mp hzc ⟨k, hk⟩)
  have hle : K ≤ involutionResidual D w := by
    have h := map_mono (f := D.subtype)
      (le_map_solvableResidual_of_isPerfect (K.subgroupOf D) (centralizer ({w} : Set D)) hKC)
    simpa only [map_subgroupOf_eq_of_le hKD, involutionResidual] using h
  have hw : orderOf w = 2 := by
    rw [← orderOf_injective D.subtype D.subtype_injective]
    change orderOf (z : G) = 2
    rw [orderOf_coe]
    exact hz
  obtain ⟨er⟩ := involutionResidual_equiv D q hq hlarge hmodel w hw
  exact eq_of_le_of_card_ge hle (le_of_eq
    ((Nat.card_congr er.toEquiv).trans (Nat.card_congr e.toEquiv).symm))

/-- The A.3.15(3) subgroup is based at an involution centralizing B; no Sylow position is asserted. -/
theorem caseThree_involutionResidual {D B S K : Subgroup G}
    {q : ℕ} [Fact q.Prime] {ε : Sign}
    (h : CaseThree D B S K q .unitary ε) (hlarge : 3 < q) :
    ∃ z : D, orderOf z = 2 ∧ (z : G) ∈ centralizer (B : Set G) ∧
      K = involutionResidual D z := by
  obtain ⟨e⟩ := h.sl2
  obtain ⟨z, hzc, hz⟩ := sl2_exists_central_involution K q h.odd_characteristic e
  let w : D := ⟨z, h.sl2_inside z.property⟩
  have hw : orderOf w = 2 := by
    rw [← orderOf_injective D.subtype D.subtype_injective]
    change orderOf (z : G) = 2
    rw [orderOf_coe]
    exact hz
  refine ⟨w, hw, ?_, sl2_eq_involutionResidual D K h.sl2_inside q
    h.odd_characteristic hlarge h.model e z hzc hz⟩
  exact le_centralizer_iff.mp
    (cyclicDecomposition_le_centralizer_centerImage h.toCyclicDecomposition) ⟨z, hzc, rfl⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
