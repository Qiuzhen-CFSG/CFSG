module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.GroupAction.Defs
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy

/-!
# Order-seven action and perfectness of the actual HS normalizer

Orbit counting shows that a nontrivial automorphism of order seven on the
marked elementary eight has only the identity fixed. A normalizer element
of order seven acts nontrivially because the action kernel has order 64.
Squaring then proves that its conjugation on the whole C₄³ core is fixed-point-free.
Cauchy's theorem supplies such an actor from the exact normalizer order.

The bijective commutator map puts the core in the normalizer's derived subgroup;
the perfect SL₃(2) quotient proves the normalizer perfect. We also transport the
existing PSL₃(2) involution class and lift the conjugator to the actual normalizer.

Source: Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423, final HS paragraph.
The orbit-counting proof follows the argument in
`SmallNonabelianTwoGroupAutomorphismOrderSevenRankThree.lean`, specialized here
without importing its unrelated two-group bounds.
-/

public section

open Subgroup MonoidHom
open scoped commutatorElement
namespace Sporadic.LeechRelated.HS.BlockNormalizer.CoreGeometry
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_eight_fixedPointFree (φ : MulAut baseElementary)
    (hpow : φ ^ 7 = 1) (hne : φ ≠ 1) : FixedPointFree φ := by
  let line := zpowers φ
  have hp : IsPGroup 7 line := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [line, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hpow)
  let fixed := FixedPoints.subgroup line baseElementary
  have hmod := hp.card_modEq_card_fixedPoints baseElementary
  change Nat.card baseElementary % 7 = Nat.card fixed % 7 at hmod
  have hle : Nat.card fixed ≤ 8 :=
    (Nat.card_le_card_of_injective (Subtype.val : fixed → baseElementary)
      Subtype.val_injective).trans_eq baseElementary_card
  have hlt : Nat.card fixed < 8 := by
    by_contra hnot
    have htop : fixed = ⊤ := fixed.eq_top_of_card_eq (by rw [baseElementary_card]; omega)
    apply hne
    apply MulEquiv.ext
    intro point
    have hmem : point ∈ fixed := htop ▸ mem_top point
    exact ((FixedPoints.mem_subgroup (M := line) (a := point)).mp hmem) ⟨φ, mem_zpowers φ⟩
  have hbot : fixed = ⊥ := card_eq_one.mp (by rw [baseElementary_card] at hmod; omega)
  intro point hpoint
  have hmem : point ∈ fixed := by
    rw [FixedPoints.mem_subgroup]
    intro actor
    exact smul_eq_self_of_mem_zpowers actor.property hpoint
  simpa [hbot] using hmem

/-- Every order-seven normalizer element acts freely off the identity on the elementary eight. -/
theorem seven_elementary_fixedPointFree (y : baseNormalizer) (hy : orderOf y = 7) :
    FixedPointFree (baseElementary.normalizerMonoidHom y) := by
  let f : baseNormalizer →* MulAut baseElementary := baseElementary.normalizerMonoidHom
  change FixedPointFree (f y)
  apply seven_eight_fixedPointFree
  · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  · intro h
    have hk : y ∈ pCore 2 baseNormalizer := by
      rw [model_core_eq_action_ker]
      exact h
    have hd := orderOf_dvd_natCard (⟨y, hk⟩ : pCore 2 baseNormalizer)
    rw [← Subgroup.orderOf_coe, hy, model_core_card] at hd
    norm_num at hd

/-- The square map lifts fixed-point-freeness to the full actual two-core. -/
theorem seven_core_fixedPointFree (y : baseNormalizer) (hy : orderOf y = 7) :
    FixedPointFree (MulAut.conjNormal (H := pCore 2 baseNormalizer) y) := by
  intro q hq
  have hs : squareHom q = 1 := seven_elementary_fixedPointFree y hy (squareHom q) (by
    rw [← squareHom_conjugation, hq])
  have hs' : (q.val : Carrier) ^ 2 = 1 := congrArg Subtype.val hs
  have hq2 : q ^ 2 = 1 := Subtype.ext (Subtype.ext hs')
  let qE : baseElementary := ⟨(q.val : Carrier), (core_involution_iff q).mp hq2⟩
  have he : qE = 1 := seven_elementary_fixedPointFree y hy qE (by
    apply Subtype.ext
    exact congrArg (fun q : pCore 2 baseNormalizer => (q.val : Carrier)) hq)
  have he' : (q.val : Carrier) = 1 := congrArg (fun x : baseElementary => (x : Carrier)) he
  apply Subtype.ext
  apply Subtype.ext
  exact he'

theorem exists_seven_fixedPointFree : ∃ y : baseNormalizer, orderOf y = 7 ∧
    FixedPointFree (MulAut.conjNormal (H := pCore 2 baseNormalizer) y) := by
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := baseNormalizer) 7 (by
    rw [normalizer_card]
    decide)
  exact ⟨y, hy, seven_core_fixedPointFree y hy⟩

theorem core_le_commutator : pCore 2 baseNormalizer ≤ _root_.commutator baseNormalizer := by
  obtain ⟨y, _, hfree⟩ := exists_seven_fixedPointFree
  intro q hq
  obtain ⟨a, ha⟩ := hfree.commutatorMap_surjective (⟨q, hq⟩ : pCore 2 baseNormalizer)
  have heq : (a : baseNormalizer) / (y * (a : baseNormalizer) * y⁻¹) = q :=
    congrArg Subtype.val ha
  rw [← heq]
  have hc := commutator_mem_commutator (mem_top (a : baseNormalizer)) (mem_top y)
  simpa only [_root_.commutator_def, commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using hc

instance normalizer_isPerfect : Group.IsPerfect baseNormalizer := by
  let e := Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two
  let := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect (MulAut baseElementary) := Group.IsPerfect.ofSurjective
    (f := baseAutomorphismEquiv.symm.toMonoidHom) baseAutomorphismEquiv.symm.surjective
  let f : baseNormalizer →* MulAut baseElementary := baseElementary.normalizerMonoidHom
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective f
    baseNormalizer_action_surjective
  have hk : f.ker = pCore 2 baseNormalizer := model_core_eq_action_ker.symm
  rw [hk, sup_eq_right.mpr core_le_commutator] at h
  exact ⟨h⟩


/-- Quotient involution fusion with a conjugator in the literal normalizer. -/
theorem quotient_involutions_conjugate
    (a b : baseNormalizer ⧸ pCore 2 baseNormalizer) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ m : baseNormalizer, QuotientGroup.mk' (pCore 2 baseNormalizer) m * a *
      (QuotientGroup.mk' (pCore 2 baseNormalizer) m)⁻¹ = b := by
  obtain ⟨f⟩ := baseNormalizer_quotient_of_surjective baseNormalizer_action_surjective
  let e := f.trans Matrix.PSL3Two.equiv
  obtain ⟨g, hg⟩ := Matrix.PSL3Two.involutions_conjugate (e a) (e b)
    ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb)
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (pCore 2 baseNormalizer) (e.symm g)
  refine ⟨m, e.injective ?_⟩
  rw [hm, map_mul, map_mul, map_inv, e.apply_symm_apply]
  exact hg

end Sporadic.LeechRelated.HS.BlockNormalizer.CoreGeometry
