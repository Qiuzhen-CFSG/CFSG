module
public import Theory.GroupAction.SymplecticRankThree.FullElations
public import Theory.SpecificGroups.PSp4Three.Generation
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.BinaryPolar

/-!
# Symplectic recognition after polar coordinatization

An arbitrary polar coordinate equivalence is enough; equivariance is proved.
The source condition-(i) kernel exhausts every pointwise polar-block fixer.
Each concrete transvection therefore belongs to the transported source action,
and symplectic transvection generation puts the full matrix group inside it.
The intrinsic classification of polar permutations proves this subgroup normal.
Taking its inverse image gives a normal subgroup of the original group and
an actual equivalence with full Sp₄, also for the binary field.

This proves the elation-generation and normal-subgroup step, conditional on
polar coordinates. Constructing those coordinates from the incidence axioms
is a separate, still necessary obligation; this is not the full Higman theorem.
No source-group simplicity or model homomorphism is assumed.

Source: Higman (1964), Theorem 2(i), p.154; Fong–Seitz II (7C), p.193.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree
open Subgroup MulAction
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Polar permutations normalize the full projective symplectic action. -/
theorem polar_conjugate_projectiveAction
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) (g : Sp F) :
    φ * projectiveAction g * φ⁻¹ ∈ (projectiveAction (F := F)).range := by
  by_cases hF : Nat.card F = 2
  · obtain ⟨t,rfl⟩ := polar_permutation_eq_projectiveAction_of_card_two hF φ hφ
    exact ⟨t*g*t⁻¹,by simp only [map_mul,map_inv]⟩
  · obtain ⟨t,σ,rfl⟩ := polar_permutation_eq_innerFieldProjective_of_card_ne_two hF φ hφ
    refine ⟨((MulAut.conj t) * DiagramAutomorphisms.fieldAutomorphism σ) g,?_⟩
    ext p
    have hh := innerFieldProjective_smul t g σ ((innerFieldProjective t σ)⁻¹ p)
    simpa only [Equiv.Perm.mul_apply,projectiveAction_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm

omit [Finite F] [CharP F 2] in
private theorem transvection_fixes_polar_block (v : Vector F) (hv : v ≠ 0) (t : F)
    (p : ProjectivePoint F) (hp : Orthogonal (Projectivization.mk F v hv) p) :
    projectiveAction (Matrix.PSp4Three.transvection v t) p = p := by
  induction p using Projectivization.ind with
  | h w hw =>
    rw [orthogonal_mk_iff] at hp
    have hp' : Matrix.PSp4Three.form v w = 0 := hp
    simp only [projectiveAction_apply,Projectivization.smul_mk,
      Matrix.PSp4Three.transvection_apply,Matrix.PSp4Three.form_swap w v,hp',
      neg_zero,mul_zero,zero_smul,add_zero]

variable {Ω G : Type*} [Finite Ω] [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
variable (C : Ω ≃ ProjectivePoint F)

/-- Transport of the actual source action through an arbitrary point equivalence. -/
@[expose] def coordinateAction : G →* Equiv.Perm (ProjectivePoint F) :=
  C.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G Ω)

omit [Finite F] [CharP F 2] [Finite Ω] [FaithfulSMul G Ω] in
@[simp] theorem coordinateAction_apply (g : G) (p : ProjectivePoint F) :
    coordinateAction C g p = C (g • C.symm p) := rfl

omit [Finite F] [CharP F 2] [Finite Ω] in
theorem coordinateAction_injective : Function.Injective (coordinateAction (G := G) C) := by
  intro g h hh
  apply eq_of_smul_eq_smul (α := Ω)
  intro x
  have hx := Equiv.congr_fun hh (C x)
  simpa only [coordinateAction_apply,C.symm_apply_apply,C.injective.eq_iff] using hx

namespace PolarityDesign
variable (D : PolarityDesign Ω (Nat.card F))
variable (hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y)
variable (hC : ∀ x y, Orthogonal (C x) (C y) ↔ D.incident x y)
include hact hC

omit [Finite F] [CharP F 2] [FaithfulSMul G Ω] in
theorem coordinateAction_preserves (g : G) (p r : ProjectivePoint F) :
    Orthogonal (coordinateAction C g p) (coordinateAction C g r) ↔ Orthogonal p r := by
  rw [coordinateAction_apply,coordinateAction_apply,hC,hact,← hC]
  simp only [C.apply_symm_apply]

omit [CharP F 2] in
/-- Condition (i) supplies every symplectic transvection, hence the whole matrix group. -/
theorem projectiveAction_le_coordinateAction [IsPretransitive G Ω]
    {a b : Ω} (hab : ¬ D.incident a b)
    (hk : Nat.card F ≤ Nat.card (fixingSubgroup G (D.block a))) :
    (projectiveAction (F := F)).range ≤ (coordinateAction (G := G) C).range := by
  have hq : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  have ht (v : Vector F) (t : F) :
      projectiveAction (Matrix.PSp4Three.transvection v t) ∈ (coordinateAction (G := G) C).range := by
    by_cases hv : v = 0
    · subst v
      rw [Matrix.PSp4Three.transvection_zero_vector,map_one]
      exact one_mem _
    let φ := C.symm.permCongrHom (projectiveAction (Matrix.PSp4Three.transvection v t))
    have hφ (x y : Ω) : D.incident (φ x) (φ y) ↔ D.incident x y := by
      rw [← hC,← hC]
      change Orthogonal (C (C.symm (Matrix.PSp4Three.transvection v t • C x))) (C (C.symm (Matrix.PSp4Three.transvection v t • C y))) ↔ _
      rw [C.apply_symm_apply,C.apply_symm_apply,orthogonal_smul_iff]
    have hf (y : Ω) (hy : y ∈ D.block (C.symm (Projectivization.mk F v hv))) : φ y = y := by
      apply C.injective
      change C (C.symm (projectiveAction (Matrix.PSp4Three.transvection v t) (C y))) = C y
      rw [C.apply_symm_apply]
      apply transvection_fixes_polar_block v hv t
      simpa only [C.apply_symm_apply] using (hC _ _).mpr hy
    obtain ⟨g,hg⟩ := D.all_block_fixers_mem_action hact hq hab hk
      (C.symm (Projectivization.mk F v hv)) φ hφ hf
    refine ⟨g,?_⟩
    ext p
    have he := Equiv.congr_fun hg (C.symm p)
    change g • C.symm p = C.symm (projectiveAction (Matrix.PSp4Three.transvection v t) (C (C.symm p))) at he
    simp only [C.apply_symm_apply] at he
    rw [coordinateAction_apply,he,C.apply_symm_apply]
  have hgen : Matrix.PSp4Three.transvectionGroup 2 F ≤
      ((coordinateAction (G := G) C).range).comap projectiveAction := by
    apply (closure_le _).mpr
    rintro g ⟨v,t,rfl⟩
    exact ht v t
  rw [Matrix.PSp4Three.transvectionGroup_eq_top] at hgen
  rintro φ ⟨g,rfl⟩
  exact hgen (mem_top g)

/-- Construct the normal full symplectic subgroup; only polar coordinatization remains explicit. -/
theorem normal_symplectic_of_coordinates [IsPretransitive G Ω]
    {a b : Ω} (hab : ¬ D.incident a b)
    (hk : Nat.card F ≤ Nat.card (fixingSubgroup G (D.block a))) :
    ∃ K : Subgroup G, K.Normal ∧ Nonempty (K ≃* Sp F) := by
  let ρ := coordinateAction (G := G) C
  let K := (projectiveAction (F := F)).range.comap ρ
  have hnormal : K.Normal := by
    refine ⟨?_⟩
    intro g hg t
    obtain ⟨u,hu⟩ := hg
    change ρ (t*g*t⁻¹) ∈ (projectiveAction (F := F)).range
    rw [map_mul,map_mul,map_inv,← hu]
    exact polar_conjugate_projectiveAction (ρ t)
      (D.coordinateAction_preserves C hact hC t) u
  let f : K →* (projectiveAction (F := F)).range :=
    (ρ.comp K.subtype).codRestrict _ (fun k => k.property)
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact coordinateAction_injective C (congrArg Subtype.val hxy)
  have hs : Function.Surjective f := by
    intro u
    obtain ⟨g,hg⟩ := D.projectiveAction_le_coordinateAction C hact hC hab hk u.property
    exact ⟨⟨g,show ρ g ∈ (projectiveAction (F := F)).range from hg.symm ▸ u.property⟩,
      Subtype.ext hg⟩
  exact ⟨K,hnormal,⟨(MulEquiv.ofBijective f ⟨hi,hs⟩).trans
    (MonoidHom.ofInjective projectiveAction_injective).symm⟩⟩

end PolarityDesign
end Theory.GroupAction.SymplecticRankThree
