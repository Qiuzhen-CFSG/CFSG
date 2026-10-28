module
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.Representation.SL2NaturalOffenders.OuterSemilinear
public import Theory.Representation.SemilinearInvolutionFixedCard
public import Mathlib.FieldTheory.Fixed

/-!
# Marked alternatives for a natural SL₂ normal component

An elementary semilinear actor with a one-dimensional binary fixed space has
coefficient field of order at most four: its coefficient image has order at
most two, and its fixed field injects into that fixed line. A nonidentity
semilinear involution moves at least the binary degree of the field. These
estimates treat the two fixed-point alternatives used in G.11.7 on the actual
normal natural component, without identifying an arbitrary extension.

Source: Aschbacher--Smith, G.11.7, printed pp.367--368.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
namespace Representation.MarkedSemilinearPlane
variable {F D : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [Finite D]

/-- A fixed binary line bounds the coefficient field of an elementary
semilinear actor by four. The actual coefficient image and fixed field are used. -/
theorem card_le_four_of_fixed_line
    (ρ : Representation (ZMod 2) D (Fin 2 → F))
    (hsemi : ∀ d : D, ∃ σ : F ≃+* F, ∀ c w, ρ d (c • w) = σ c • ρ d w)
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    (v : Fin 2 → F) (hv : v ≠ 0)
    (hfix : fixedSpace ρ A = Submodule.span (ZMod 2) {v}) : Nat.card F ≤ 4 := by
  classical
  let φ : A →* (F ≃+* F) := (SL2NaturalOffenders.fieldAction ρ hsemi).comp A.subtype
  let C := φ.range
  let : Finite C := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let := Fintype.ofFinite C
  let : FaithfulSMul C F := ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩
  let K := FixedPoints.subfield C F
  have hc : Nat.card C ≤ 2 := SL2NaturalOffenders.fieldAction_range_card_le_two A inferInstance φ
  have hdegree : Module.finrank K F = Nat.card C := by
    simpa only [K,Nat.card_eq_fintype_card] using FixedPoints.finrank_eq_card C F
  have hvfix : v ∈ fixedSpace ρ A := hfix ▸ Submodule.mem_span_singleton_self v
  let f : K → fixedSpace ρ A := fun c => ⟨(c : F) • v,by
    intro a
    change ρ (a : D) ((c : F) • v) = (c : F) • v
    rw [SL2NaturalOffenders.fieldAction_smul ρ hsemi,show ρ (a : D) v = v from hvfix a]
    change φ a (c : F) • v = (c : F) • v
    rw [show φ a (c : F) = (c : F) from c.property ⟨φ a,⟨a,rfl⟩⟩]⟩
  have hfi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (smul_left_injective F hv (congrArg Subtype.val he))
  have hk := Nat.card_le_card_of_injective f hfi
  rw [hfix,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Submodule.span (ZMod 2) {v}),finrank_span_singleton hv,
    Nat.card_zmod,pow_one] at hk
  calc
    Nat.card F = Nat.card K ^ Nat.card C := by
      rw [Module.natCard_eq_pow_finrank (K := K),hdegree]
    _ ≤ 2 ^ Nat.card C := Nat.pow_le_pow_left hk _
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hc
    _ = 4 := by norm_num

omit [Finite D] in
/-- Every nonidentity semilinear involution of a field plane moves at least
one binary field degree. -/
theorem degree_le_involution_displacement
    (ρ : Representation (ZMod 2) D (Fin 2 → F)) (hf : Function.Injective ρ)
    (hsemi : ∀ d : D, ∃ σ : F ≃+* F, ∀ c w, ρ d (c • w) = σ c • ρ d w)
    (a : D) (ha : a ≠ 1) (ha2 : a^2 = 1)
    (n : ℕ) (hF : Nat.card F = 2^n) :
    n ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
  classical
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨σ,hσ⟩ := hsemi a
  by_cases hs : σ = RingEquiv.refl F
  · have hl (c : F) (w : Fin 2 → F) : ρ a (c • w) = c • ρ a w := by
      simpa only [hs,RingEquiv.refl_apply] using hσ c w
    obtain ⟨w,hw⟩ : ∃ w, ρ a w ≠ w := by
      by_contra! hall
      apply ha
      apply hf
      simpa only [map_one, Module.End.one_apply] using (LinearMap.ext hall : ρ a = 1)
    let f : F → LinearMap.range (ρ a - 1) := fun c =>
      ⟨c • (ρ a w - w),⟨c • w,by simp only [LinearMap.sub_apply,Module.End.one_apply,hl,smul_sub]⟩⟩
    have hi : Function.Injective f := by
      intro c d he
      exact smul_left_injective F (sub_ne_zero.mpr hw) (congrArg Subtype.val he)
    have hc := Nat.card_le_card_of_injective f hi
    rw [hF,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc
  · let E := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
    have hinv : Function.Involutive E := by
      intro w
      change ρ a (ρ a w) = w
      rw [← Module.End.mul_apply,← map_mul,← pow_two,ha2,map_one]
      rfl
    have hsi := SL2NaturalOffenders.semilinear_coefficient_involutive E hinv σ hσ
    have hcount := SemilinearInvolution.fixed_card_sq σ hsi hs E.toAddMonoidHom hinv hσ
    let U := (ρ a - 1).ker
    have heq : U.toAddSubgroup = E.toAddMonoidHom.eqLocus (AddMonoidHom.id _) := by
      ext w
      change ρ a w - w = 0 ↔ ρ a w = w
      exact sub_eq_zero
    have hcard : Nat.card U ^ 2 = Nat.card (Fin 2 → F) := by
      change Nat.card U.toAddSubgroup ^ 2 = _
      rw [heq]
      exact hcount
    rw [Nat.card_fun,Nat.card_fin,hF,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,← pow_mul,← pow_mul] at hcard
    have hk := (Nat.pow_right_injective (by decide : 2≤2)) hcard
    have hd := (ρ a - 1).finrank_range_add_finrank_ker
    have hdim : Module.finrank (ZMod 2) (Fin 2 → F) = 2*n := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
      rw [Nat.card_zmod,hF] at hc
      have he := (Nat.pow_right_injective (by decide : 2≤2)) hc
      simp [Module.finrank_pi_fintype,←he]
    change Module.finrank (ZMod 2) U * 2 = n*2 at hk
    dsimp only [U] at hk
    omega
end Representation.MarkedSemilinearPlane

namespace Representation.MarkedSemilinearPlane
open scoped MatrixGroups
open Subgroup Representation.BinaryOffender
variable {F D V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]

/-- A natural SL₂ normal component with either source fixed-point alternative
has defining field of order at most four. All actors and coordinates are literal. -/
theorem card_le_four_of_natural_normal_component
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (L : Subgroup D) [L.Normal] (e : L ≃* SL(2,F))
    (c : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (hcoord : ∀ (l : L) w, c (ρ l w) = (e l).val.mulVec (c w))
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    (v : V) (hv : v ≠ 0)
    (halt : fixedSpace ρ A = Submodule.span (ZMod 2) {v} ∨
      ∃ a : A, a ≠ 1 ∧ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2)
    (n : ℕ) (hF : Nat.card F = 2^n) : Nat.card F ≤ 4 := by
  classical
  let τ : Representation (ZMod 2) D (Fin 2 → F) := c.conjRingEquiv.toMonoidHom.comp ρ
  have ht (a : D) (w : Fin 2 → F) : τ a w = c (ρ a (c.symm w)) := rfl
  have ht' (a : D) (w : V) : τ a (c w) = c (ρ a w) := by rw [ht,c.symm_apply_apply]
  have htf : Function.Injective τ := by
    intro a b he
    apply hf
    apply c.conjRingEquiv.injective
    exact he
  have hnat (l : L) (w : Fin 2 → F) : τ l w = (e l).val.mulVec w := by
    rw [ht,hcoord,c.apply_symm_apply]
  have hsemi := SL2NaturalOffenders.normalizer_semilinear L e τ hnat
  rcases halt with hfix | ⟨a,ha,hr⟩
  · have hline : fixedSpace τ A = Submodule.span (ZMod 2) {c v} := by
      ext w
      constructor
      · intro hw
        have hh : c.symm w ∈ fixedSpace ρ A := by
          intro a
          change ρ (a : D) (c.symm w) = c.symm w
          apply c.injective
          rw [← ht,show τ (a : D) w = w from hw a,c.apply_symm_apply]
        rw [hfix,Submodule.mem_span_singleton] at hh
        obtain ⟨r,hr⟩ := hh
        apply Submodule.mem_span_singleton.mpr
        refine ⟨r,?_⟩
        rw [← c.map_smul,hr,c.apply_symm_apply]
      · intro hw a
        obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hw
        have hvfix : ρ (a : D) v = v := (hfix ▸ Submodule.mem_span_singleton_self v) a
        change τ (a : D) (r • c v) = r • c v
        rw [map_smul,ht',hvfix]
    exact card_le_four_of_fixed_line τ hsemi A (c v) (fun he => hv (c.injective (he.trans c.map_zero.symm))) hline
  · have hm : (LinearMap.range (ρ (a : D) - 1)).map c.toLinearMap =
        LinearMap.range (τ (a : D) - 1) := by
      ext w
      constructor
      · rintro ⟨u,⟨z,rfl⟩,rfl⟩
        refine ⟨c z,?_⟩
        simp only [LinearMap.sub_apply,Module.End.one_apply,LinearEquiv.coe_coe,map_sub,ht']
      · rintro ⟨z,rfl⟩
        refine ⟨ρ (a : D) (c.symm z) - c.symm z,⟨c.symm z,rfl⟩,?_⟩
        simp only [LinearMap.sub_apply,Module.End.one_apply,LinearEquiv.coe_coe,map_sub,← ht,c.apply_symm_apply]
    have hr' : Module.finrank (ZMod 2) (LinearMap.range (τ (a : D) - 1)) ≤ 2 := by
      rw [← hm,c.finrank_map_eq]
      exact hr
    have ha1 : (a : D) ≠ 1 := fun he => ha (Subtype.ext he)
    have ha2 : (a : D)^2 = 1 := congrArg Subtype.val
      ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)) a)
    have hb := degree_le_involution_displacement τ htf hsemi a ha1 ha2 n hF
    calc
      Nat.card F = 2^n := hF
      _ ≤ 2^2 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 4 := by norm_num
end Representation.MarkedSemilinearPlane
