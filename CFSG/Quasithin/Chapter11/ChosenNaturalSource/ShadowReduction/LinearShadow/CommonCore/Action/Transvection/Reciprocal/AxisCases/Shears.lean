module
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Full shears and special-linear plane transport

A field-linear automorphism fixing a hyperplane and inducing the identity
on its quotient is determined by its displacement at one outside vector.
This bounds the full shear group by the order of the hyperplane. Conjugation
transports this literal group. Dual functionals and determinant-one matrix
transitivity transport any plane in three-space to any other plane.

These are the linear-algebra steps in the actual doubled-action comparison
of `AxisCases.SL3`. Source: Aschbacher--Smith 11.3.7(4), case (ii),
refs/quasithin.pdf, printed p.773.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Subgroup Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
namespace Shear
variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

def group (U : Submodule F E) : Subgroup (E ≃ₗ[F] E) where
  carrier := {e | (∀ v ∈ U, e v = v) ∧ ∀ v, e v - v ∈ U}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro e f ⟨he,he'⟩ ⟨hf,hf'⟩
    refine ⟨fun v hv => (congrArg e (hf v hv)).trans (he v hv), fun v => ?_⟩
    have h := U.add_mem (he' (f v)) (hf' v)
    simpa only [LinearEquiv.mul_apply, sub_add_sub_cancel] using h
  inv_mem' := by
    rintro e ⟨he,he'⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · change e.symm v = v
      apply e.injective
      rw [e.apply_symm_apply]
      exact (he v hv).symm
    · change e.symm v - v ∈ U
      have h := U.neg_mem (he' (e.symm v))
      simpa only [e.apply_symm_apply, neg_sub] using h

theorem card_le [Finite F] [Finite E] [FiniteDimensional F E]
    (U : Submodule F E) (hd : Module.finrank F (E ⧸ U) = 1) :
    Nat.card (group U) ≤ Nat.card U := by
  have hUt : U ≠ ⊤ := by
    intro h
    have hh := U.finrank_quotient_add_finrank
    rw [hd,h,finrank_top] at hh
    omega
  obtain ⟨v,hv⟩ := SetLike.exists_not_mem_of_ne_top U hUt rfl
  let j : group U → U := fun e => ⟨e.val v-v,e.property.2 v⟩
  apply Nat.card_le_card_of_injective j
  intro e f h
  have hev : e.val v = f.val v := sub_left_injective (congrArg Subtype.val h)
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro x
  have htop := (Submodule.sup_span_singleton_eq_top_iff hv).mpr hd
  have hx : x ∈ U ⊔ Submodule.span F {v} := htop ▸ Submodule.mem_top
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp only [LinearEquiv.coe_coe, map_add, map_smul, e.property.1 u hu,
    f.property.1 u hu, hev]

theorem conj (U : Submodule F E) (e : E ≃ₗ[F] E) :
    (group U).map (MulAut.conj e).toMonoidHom = group (U.map e.toLinearMap) := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨?_,?_⟩
    · rintro v ⟨u,hu,rfl⟩
      change e (a (e.symm (e u))) = e u
      rw [e.symm_apply_apply,ha.1 u hu]
    · intro v
      rw [Submodule.mem_map_equiv]
      change e.symm (e (a (e.symm v))-v) ∈ U
      rw [map_sub,e.symm_apply_apply]
      exact ha.2 (e.symm v)
  · intro hb
    refine ⟨e⁻¹*b*e,⟨?_,?_⟩,by simp [MulAut.conj_apply,mul_assoc]⟩
    · intro v hv
      change e.symm (b (e v)) = v
      rw [hb.1 (e v) ⟨v,hv,rfl⟩,e.symm_apply_apply]
    · intro v
      have h := hb.2 (e v)
      rw [Submodule.mem_map_equiv] at h
      change e.symm (b (e v)-e v) ∈ U at h
      change e.symm (b (e v)) - v ∈ U
      simpa only [map_sub,e.symm_apply_apply] using h
end Shear
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal

open Subgroup Matrix Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {F : Type*} [Field F]
private theorem functional_of_plane (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 2) :
    ∃ φ : Module.Dual F (Fin 3 → F), φ ≠ 0 ∧ φ.ker = P := by
  have htop : P < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he; rw [he,finrank_top,Module.finrank_fin_fun] at hP; omega)
  obtain ⟨φ,hφ,hle⟩ := P.exists_le_ker_of_lt_top htop
  refine ⟨φ,hφ,(Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  have hd := φ.finrank_range_add_finrank_ker
  rw [Module.Dual.range_eq_top_of_ne_zero hφ,finrank_top,Module.finrank_self,
    Module.finrank_fin_fun] at hd
  omega

private theorem functional_row (φ : Module.Dual F (Fin 3 → F)) (v : Fin 3 → F) :
    φ v = (fun i => φ (Pi.single i 1)) ⬝ᵥ v := by
  have he : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,dotProduct,Fin.sum_univ_three]
  ring

private theorem functional_row_ne (φ : Module.Dual F (Fin 3 → F)) (hφ : φ ≠ 0) :
    (fun i => φ (Pi.single i 1)) ≠ 0 := by
  intro he
  apply hφ
  apply LinearMap.ext
  intro v
  rw [functional_row,he,zero_dotProduct]
  rfl

/-- A determinant-one element carries any field plane to any other field plane. -/
theorem sl3_plane_orbit (P Q : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 2) (hQ : Module.finrank F Q = 2) :
    ∃ z : SL(3,F), P.map (specialLinearNatural 3 z) = Q := by
  obtain ⟨φ,hφ,rfl⟩ := functional_of_plane P hP
  obtain ⟨ψ,hψ,rfl⟩ := functional_of_plane Q hQ
  obtain ⟨k,hk⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (fun i => ψ (Pi.single i 1)) (fun i => φ (Pi.single i 1))
    (functional_row_ne ψ hψ) (functional_row_ne φ hφ)
  let z := k.transpose
  have he (v : Fin 3 → F) : ψ (specialLinearNatural 3 z v) = φ v := by
    rw [functional_row ψ,functional_row φ]
    change _ ⬝ᵥ (k.val.transpose *ᵥ v) = _
    rw [dotProduct_mulVec,vecMul_transpose,hk]
  refine ⟨z,?_⟩
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    change ψ (specialLinearNatural 3 z u) = 0
    rw [he]
    exact hu
  · intro hv
    refine ⟨specialLinearNatural 3 z⁻¹ v,?_,?_⟩
    · change φ (specialLinearNatural 3 z⁻¹ v) = 0
      rw [←he,self_inv_apply]
      exact hv
    · exact self_inv_apply (specialLinearNatural 3) z v
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
