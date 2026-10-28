module
public import Theory.SpecificGroups.PSL3.BorelCubicAction
public import Theory.SpecificGroups.PSL3.CartanActions.BorelResidual
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreImage

/-!
# Inner two-elements detected on a lifted large linear Borel

For a finite group with PSL₃(2ⁿ) two-core quotient, n ≥ 3, the residual
of its prescribed Sylow normalizer maps onto the entire quotient Borel.
A two-element preserving that Sylow and fixing the residual modulo its
own two-core therefore fixes the quotient torus. The proved cubic Borel
action calculation makes its action on the literal quotient inner.

The original two-core extension is retained; no complement is chosen.
Source: Aschbacher–Smith 14.7.41, printed p.1061, refs/quasithin.pdf;
the automorphism calculation is the one also used in 12.6.31.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LiftedBorelInner
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions.BorelQuotient
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A two-element fixing the full Borel quotient is inner at the given Sylow. -/
theorem inner_of_sylow_borel_fixed_three {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F))
    (ha : ∃ k : ℕ, a ^ (2^k) = 1)
    (hP : (P : Subgroup PSL(3,F)).map a.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set PSL(3,F)), a x * x⁻¹ ∈ P) :
    a ∈ MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P
    (unipotentSylow F (by omega : 0 < n) hF)
  let e := MulAut.conj g
  have hPe : (P : Subgroup PSL(3,F)).map e.toMonoidHom = unipotent F := by
    change ((g • P : Sylow 2 PSL(3,F)) : Subgroup PSL(3,F)) = _
    rw [hg]
    rfl
  let b := MulAut.congr e a
  have hact (x : PSL(3,F)) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = _
    rw [e.symm_apply_apply]
  have hU : (unipotent F).map b.toMonoidHom = unipotent F := by
    have heq : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom :=
      MonoidHom.ext hact
    rw [←hPe,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  have hN : (normalizer (P : Set PSL(3,F))).map e.toMonoidHom = borel F := by
    change (normalizer ((P : Subgroup PSL(3,F)) : Set PSL(3,F))).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hPe,normalizer_unipotent F (by omega) hF]
  have hbc : ∀ x ∈ borel F, (b x * x⁻¹)^3 ∈ unipotent F := by
    intro x hx
    rw [←hN] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem e.toMonoidHom (hc y hy)
    rw [hPe] at hh
    apply pow_mem
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom,hact] using hh
  have hbp : ∃ k : ℕ, b ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := ha
    exact ⟨k,by rw [show b = MulAut.congr e a from rfl,←map_pow,hk,map_one]⟩
  obtain ⟨x,hx⟩ := BorelCubicAction.inner_of_cubic_displacement_three hn hF b hbp hU hbc
  refine ⟨e.symm x,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hx

/-- The original large-field API. -/
theorem inner_of_sylow_borel_fixed {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F))
    (ha : ∃ k : ℕ, a ^ (2^k) = 1)
    (hP : (P : Subgroup PSL(3,F)).map a.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set PSL(3,F)), a x * x⁻¹ ∈ P) :
    a ∈ MulAut.innerSubgroup PSL(3,F) :=
  inner_of_sylow_borel_fixed_three (by omega) hF P a ha hP hc

variable {H : Type*} [Group H] [Finite H]

/-- Lift the Borel detector through the whole intrinsic two-core. -/
theorem quotient_inner_of_borelResidual_fixed_three {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 3 ≤ n) (e : (H ⧸ pCore 2 H) ≃* PSL(3,F))
    (P : Sylow 2 H) (α : MulAut H)
    (hα : ∃ k : ℕ, α ^ (2^k) = 1)
    (hP : (P : Subgroup H).map α.toMonoidHom = P)
    (hfix : ∀ b ∈ (pResidual 2 (normalizer (P : Set H))).map
        (normalizer (P : Set H)).subtype,
      b⁻¹ * α b ∈ ((pResidual 2 (normalizer (P : Set H))).map
        (normalizer (P : Set H)).subtype).pCoreIn 2) :
    (pCore 2 H).quotientAut α ∈ MulAut.innerSubgroup (H ⧸ pCore 2 H) := by
  let f : H →* PSL(3,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let Q := P.mapSurjective hf
  let β := MulAut.congr e ((pCore 2 H).quotientAut α)
  have heq (x : H) : β (f x) = f (α x) := by
    change e ((pCore 2 H).quotientAut α (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hQ : (Q : Subgroup PSL(3,F)).map β.toMonoidHom = Q := by
    have he : β.toMonoidHom.comp f = f.comp α.toMonoidHom := MonoidHom.ext heq
    change ((P : Subgroup H).map f).map β.toMonoidHom = (P : Subgroup H).map f
    rw [Subgroup.map_map,he,←Subgroup.map_map,hP]
  let B := (pResidual 2 (normalizer (P : Set H))).map (normalizer (P : Set H)).subtype
  have hBN : B.map f = normalizer (Q : Set PSL(3,F)) := by
    have hp := sylowNormalizer_twoResidual F (by omega : 0 < n) hF
      (show 2 < Nat.card F by
        rw [hF]
        exact (by decide : 2 < 2^2).trans_le
          (Nat.pow_le_pow_right (by decide) (by omega))) Q
    change ((pResidual 2 (normalizer (P : Set H))).map _).map f = _
    rw [map_embedded_pResidual,P.normalizer_map_surjective f hf]
    change (pResidual 2 (normalizer (Q : Set PSL(3,F)))).map _ = _
    rw [hp]
    exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)
  have hBQ : (B.pCoreIn 2).map f ≤ (Q : Subgroup PSL(3,F)) := by
    rw [map_pCoreIn_of_ker_isPGroup f hk,hBN]
    have hh := pCoreIn_le_sylow (normalizer (Q : Set PSL(3,F)))
      (Q.subtype (Q : Subgroup PSL(3,F)).le_normalizer)
    rw [Sylow.coe_subtype] at hh
    exact hh.trans_eq (map_subgroupOf_eq_of_le (Q : Subgroup PSL(3,F)).le_normalizer)
  have hβ : ∃ k : ℕ, β ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := hα
    refine ⟨k,?_⟩
    change (MulAut.congr e ((pCore 2 H).quotientAut α)) ^ (2^k) = 1
    rw [←map_pow,←map_pow,hk,map_one,map_one]
  have hb := inner_of_sylow_borel_fixed_three hn hF Q β hβ hQ (by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := hBN.ge hx
    have hd : (f b)⁻¹ * β (f b) ∈ Q := by
      rw [heq,←map_inv,←map_mul]
      exact hBQ (mem_map_of_mem f (hfix b hb))
    have hnQ : f b ∈ normalizer (Q : Set PSL(3,F)) := hBN.le (mem_map_of_mem f hb)
    have hh := (mem_normalizer_iff.mp hnQ _).mp hd
    change β (f b) * (f b)⁻¹ ∈ (Q : Subgroup PSL(3,F))
    simpa only [mul_inv_cancel_left] using hh)
  obtain ⟨g,hg⟩ := hb
  refine ⟨e.symm g,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hg

/-- The original large-field lifted detector. -/
theorem quotient_inner_of_borelResidual_fixed {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 4 ≤ n) (e : (H ⧸ pCore 2 H) ≃* PSL(3,F))
    (P : Sylow 2 H) (α : MulAut H)
    (hα : ∃ k : ℕ, α ^ (2^k) = 1)
    (hP : (P : Subgroup H).map α.toMonoidHom = P)
    (hfix : ∀ b ∈ (pResidual 2 (normalizer (P : Set H))).map
        (normalizer (P : Set H)).subtype,
      b⁻¹ * α b ∈ ((pResidual 2 (normalizer (P : Set H))).map
        (normalizer (P : Set H)).subtype).pCoreIn 2) :
    (pCore 2 H).quotientAut α ∈ MulAut.innerSubgroup (H ⧸ pCore 2 H) :=
  quotient_inner_of_borelResidual_fixed_three hF (by omega) e P α hα hP hfix

end Matrix.PSL3.LiftedBorelInner
