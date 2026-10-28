module
public import Theory.Representation.NormalElementaryQuotient.NaturalNormalSubgroup
public import Theory.Representation.SL2NaturalFixedLifting
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.Module.ZMod

/-!
# Noncentral fixed vectors in the moving part of a natural extension

An elementary normal module mapping onto the natural SL₂ plane has its
whole plane covered by the actor commutator: one transvection displacement
and transitivity on nonzero vectors suffice. A two-subgroup has a nonzero
fixed vector on that plane. Fixed-point lifting through the full central
kernel then gives a noncentral fixed vector in the original commutator.
No splitting of the central extension is assumed.

Source application: DGS, Groups and Graphs (1985), (6.5), pp.121--122,
through PushingUp.BaumannBinary.AmbientNaturalCenter.
-/

open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
public noncomputable section
namespace Representation.NormalElementaryQuotient
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
variable [Algebra (ZMod 2) F]

omit [Finite G] [Finite F] [CharP F 2] in
theorem natural_projection_movement_surjective
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (f : Additive V →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
      Matrix.mulVec (q g).val (f v)) :
    ∀ u, ∃ v : Additive V, (v.toMul : G) ∈ ⁅V, (⊤ : Subgroup G)⁆ ∧ f v = u := by
  let W := ⁅V, (⊤ : Subgroup G)⁆
  obtain ⟨v,hv⟩ := hf ![0,1]
  obtain ⟨g,hg⟩ := hq (Matrix.SpecialLinearGroup.transvection
    (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F))
  let w : Additive V := Additive.ofMul (MulAut.conjNormal g v.toMul) - v
  have hw : (w.toMul : G) ∈ W := by
    change (g * (v.toMul : G) * g⁻¹) / (v.toMul : G) ∈ ⁅V, (⊤ : Subgroup G)⁆
    rw [div_eq_mul_inv]
    change ⁅g,(v.toMul : G)⁆ ∈ ⁅V, (⊤ : Subgroup G)⁆
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_top g) v.toMul.property
  have hfw : f w = ![1,0] := by
    dsimp only [w]
    rw [map_sub,he,hv,hg]
    ext i
    fin_cases i <;> simp [Matrix.SpecialLinearGroup.transvection_coe,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two]
  intro u
  by_cases hu : u = 0
  · subst u; exact ⟨0, by simp, map_zero f⟩
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq F ![1,0] u
    (by intro hh; have := congrFun hh 0; simp at this) hu
  obtain ⟨x,rfl⟩ := hq a
  refine ⟨Additive.ofMul (MulAut.conjNormal x w.toMul),
    (inferInstance : W.Normal).conj_mem _ hw x, ?_⟩
  rw [he,hfw]
  exact ha

theorem natural_projection_movement_fixed_nonzero
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (f : Additive V →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (hker : ∀ v, f v = 0 ↔ (v.toMul : G) ∈ center G)
    (he : ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
      Matrix.mulVec (q g).val (f v))
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    ∃ v : Additive V, (v.toMul : G) ∈ ⁅V,(⊤ : Subgroup G)⁆ ∧
      (v.toMul : G) ∈ centralizer (A : Set G) ∧ f v ≠ 0 := by
  let ρ := representation V q hq hk
  have hr (g : G) (v : Additive V) :
      ρ (q g) v = Additive.ofMul (MulAut.conjNormal g v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact representation_apply V q hq hk g v
  have he' (g : SL(2,F)) (v : Additive V) : f (ρ g v) = g • f v := by
    obtain ⟨x,rfl⟩ := hq g
    rw [hr,he]
    rfl
  have hc (v : Additive V) (hv : f v = 0) (g : SL(2,F)) : ρ g v = v := by
    obtain ⟨x,rfl⟩ := hq g
    rw [hr]
    apply Additive.toMul.injective
    apply Subtype.ext
    change x * (v.toMul : G) * x⁻¹ = v.toMul
    rw [(mem_center_iff.mp ((hker v).mp hv)) x,mul_inv_cancel_right]
  let σ : Representation (ZMod 2) A (Fin 2 → F) :=
    ((specialLinearNatural 2 (k := F)).restrictScalars (k := ZMod 2)).comp (q.comp A.subtype)
  obtain ⟨u,hu,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide : ringChar (ZMod 2) ≠ 0)
    (by rwa [ringChar.eq (ZMod 2) 2] : IsPGroup (ringChar (ZMod 2)) A) σ
  obtain ⟨v,hv,hfv⟩ := natural_projection_movement_surjective V q hq f hf he u
  refine ⟨v,hv,?_,hfv ▸ hu⟩
  intro a ha
  have hp : f (ρ (q a) v) = f v := by
    rw [he',hfv]
    exact hfix ⟨a,ha⟩
  have heq := SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel ρ f.toAddMonoidHom hf he' hc (q a) v hp
  have hh := congrArg (fun w : Additive V => (w.toMul : G)) heq
  rw [hr] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
end Representation.NormalElementaryQuotient
