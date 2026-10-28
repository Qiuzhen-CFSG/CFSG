module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.A7
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.Representation.AlternatingSevenFiveRestriction.PermutationObstruction
/-!
# Excluding an alternating-five block inside an exceptional A₇ block

The actual inclusion and its two-core quotient place the smaller actor in A₇.
The order-sixteen bound identifies its full commutator layer with its specified
five-point module. Its nonzero cubic-fixed vector contradicts the fixed-free
three-cycles of the exceptional four-space. The full Sylow normalizer is
retained, and the companion source quotient module constructs these inputs.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
open ExceptionalRestrictions
variable {L : Type*} [Group L]

theorem short_u_faithful (h : IsShort L) :
    letI := h.elementary
    Function.Injective (uRepresentation h) := by
  let := h.elementary
  apply (uRepresentation h).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro g hg
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [← h.centralizer_blockU]
  intro u hu
  have he := congrArg (fun f : Module.End (ZMod 2) (Additive (blockU L)) =>
    ((f (Additive.ofMul ⟨u,hu⟩)).toMul : L)) hg
  change ((uRepresentation h (QuotientGroup.mk' (pCore 2 L) l)
    (Additive.ofMul ⟨u,hu⟩)).toMul : L) = u at he
  rw [uRepresentation_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

variable {K : Type*} [Group K] [Finite K] [Finite L]
theorem no_alternating_five_in_exceptional
    (hK : IsAlternatingBlock K 5) (hL : IsExceptionalA7Block L)
    (f : K →* L) (hf : Function.Injective f)
    (hU : (blockU K).map f ≤ blockU L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (hk : ((QuotientGroup.mk' (pCore 2 L)).comp f).ker = pCore 2 K)
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hS : (S : Subgroup _) ≤ normalizer
      ((eL.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp f)).range : Set (alternatingGroup (Fin 7)))) : False := by
  let := hK.2.1.elementary
  let := hL.1.elementary
  obtain ⟨rK, ⟨mK⟩, hmK⟩ := hK.2.2
  let qK := QuotientGroup.mk' (pCore 2 K)
  let qL := QuotientGroup.mk' (pCore 2 L)
  let a := eL.toMonoidHom.comp (qL.comp f)
  let B := a.range
  have hka : a.ker = pCore 2 K := by
    ext k
    change eL (qL (f k)) = 1 ↔ k ∈ pCore 2 K
    rw [map_eq_one_iff _ eL.injective]
    exact show qL (f k) = 1 ↔ k ∈ pCore 2 K from by rw [← hk]; rfl
  let eKB : (K ⧸ pCore 2 K) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hka.symm).trans
      (QuotientGroup.quotientKerEquivRange a)
  let eB : B ≃* alternatingGroup (Fin 5) := eKB.symm.trans mK.quotientIso
  let jU : blockU K →* blockU L :=
    (f.comp (blockU K).subtype).codRestrict _ (fun u => hU ⟨u,u.property,rfl⟩)
  have hjU : Function.Injective jU := by
    intro u v h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hcK : Nat.card (blockU K) = 16 := by
    have hle := Nat.card_le_card_of_injective jU hjU
    rw [hL.u_card] at hle
    have hlo := Nat.card_le_card_of_surjective (QuotientGroup.mk' (blockFixed K))
      (QuotientGroup.mk'_surjective (blockFixed K))
    change Nat.card (BlockModule K) ≤ Nat.card (blockU K) at hlo
    rw [hK.module_card_odd (by decide)] at hlo
    norm_num at hlo
    omega
  let p : blockU K →* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
    mK.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed K))
  have hp : Function.Surjective p := mK.moduleIso.surjective.comp
    (QuotientGroup.mk'_surjective (blockFixed K))
  have hpi : Function.Injective p := by
    apply (Nat.bijective_iff_surjective_and_card p).mpr ⟨hp,?_⟩ |>.injective
    rw [hcK]
    change 16 = Nat.card (BinaryPermutation.natural (Fin 5))
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      BinaryPermutation.finrank_natural_odd _ (by decide)]
    decide
  let ep := MulEquiv.ofBijective p ⟨hpi,hp⟩
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let j : BinaryPermutation.core (Fin 5) →+ Additive (blockU L) := {
    toFun := fun v => Additive.ofMul (jU (ep.symm (Multiplicative.ofAdd (c v))))
    map_zero' := by change Additive.ofMul (jU (ep.symm (Multiplicative.ofAdd (c 0)))) = 0; simp
    map_add' := fun v w => by
      change Additive.ofMul (jU (ep.symm (Multiplicative.ofAdd (c (v+w))))) = _
      rw [map_add]
      change Additive.ofMul (jU (ep.symm (Multiplicative.ofAdd (c v) * Multiplicative.ofAdd (c w)))) = _
      rw [map_mul, map_mul]
      rfl }
  have hj : Function.Injective j := hjU.comp (ep.symm.injective.comp c.injective)
  let ρ := (uRepresentation hL.1).comp eL.symm.toMonoidHom
  have hρ : Function.Injective ρ := (short_u_faithful hL.1).comp eL.symm.injective
  have hd : Module.finrank (ZMod 2) (Additive (blockU L)) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive (blockU L)) = Nat.card (Additive (blockU L)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      _ = 2 ^ 4 := (Nat.card_congr Additive.toMul).trans hL.u_card
  apply Representation.AlternatingSevenFiveRestriction.no_permutation_core_injection
    ρ hρ hd B eB S hS j hj
  intro b v
  obtain ⟨k, hkB⟩ := a.rangeRestrict_surjective b
  subst b
  have heKB : eKB (qK k) = a.rangeRestrict k := rfl
  have heB : eB (a.rangeRestrict k) = mK.quotientIso (qK k) := by
    change mK.quotientIso (eKB.symm (a.rangeRestrict k)) = _
    rw [← heKB, eKB.symm_apply_apply]
  let u := ep.symm (Multiplicative.ofAdd (c v))
  have hpU : p u = Multiplicative.ofAdd (c v) := ep.apply_symm_apply _
  have hpC : p (blockConjugate K k u) =
      Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 5)
        (mK.quotientIso (qK k)).val (c v)) := by
    change mK.moduleIso (QuotientGroup.mk' (blockFixed K) (blockConjugate K k u)) = _
    rw [mK.intertwining]
    apply Multiplicative.toAdd.injective
    rw [hmK]
    change BinaryPermutation.naturalRepresentation (Fin 5)
      (mK.quotientIso (qK k)).val (p u).toAdd = _
    rw [hpU]
    rfl
  have huC : blockConjugate K k u = ep.symm (Multiplicative.ofAdd
      (c (BinaryPermutation.coreRepresentation (Fin 5) (mK.quotientIso (qK k)).val v))) := by
    apply hpi
    rw [hpC, show p (ep.symm _) = _ from ep.apply_symm_apply _]
    exact congrArg Multiplicative.ofAdd (BinaryPermutation.coreEquivNatural_equivariant
      (Fin 5) (by decide) (mK.quotientIso (qK k)).val v).symm
  rw [heB]
  change uRepresentation hL.1 (eL.symm (eL (qL (f k)))) (Additive.ofMul (jU u)) = _
  rw [eL.symm_apply_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [uRepresentation_apply]
  change f k * f u.val * (f k)⁻¹ = f (ep.symm _).val
  rw [← huC]
  change f k * f u.val * (f k)⁻¹ = f (k * u.val * k⁻¹)
  simp only [map_mul, map_inv]
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
