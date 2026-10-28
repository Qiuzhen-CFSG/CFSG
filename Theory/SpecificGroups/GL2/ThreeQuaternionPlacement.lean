module

public import Theory.GroupTheory.SpecificGroups.QuaternionProduct
public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness
public import Mathlib.GroupTheory.PGroup

/-!
# Quaternion placement through a ternary matrix image

An embedded Q₈ in GL₂(3) × A, with A abelian, projects injectively to GL₂(3).
Its matrices are therefore I, -I, or square roots of -I, by the existing
kernel-checked uniqueness calculation. If a homomorphism into that product
has three-group kernel, it is injective on any quaternion subgroup. Thus
membership of these eight matrix fibers in K implies quaternion containment
in K.

This reduction is for the graph-field centralizer of PSL₃(4) in the proof
of Aschbacher–Smith 16.4.9(2), printed p.1192. The actual centralizer map,
its kernel, and the identification of the eight fibers must be constructed
separately. Determinant one alone does not identify those fibers.
-/

public section

open Subgroup
namespace Matrix.GeneralLinearGroup

/-- The GL₂(3) projection of any embedded Q₈ has the eight quaternion matrices. -/
theorem three_quaternion_prod_image {A : Type*} [CommGroup A]
    (f : QuaternionGroup 2 →* GL (Fin 2) (ZMod 3) × A)
    (hf : Function.Injective f) (x : QuaternionGroup 2) :
    (f x).1.val = 1 ∨ (f x).1.val = -1 ∨ (f x).1.val ^ 2 = -1 := by
  let g := (MonoidHom.fst (GL (Fin 2) (ZMod 3)) A).comp f
  have hg : Function.Injective g := QuaternionGroup.injective_fst_of_injective_prod f hf
  have he : Nonempty (g.range ≃* QuaternionGroup 2) := ⟨(MonoidHom.ofInjective hg).symm⟩
  exact (three_mem_quaternion_iff g.range he (g x)).mp ⟨x, rfl⟩

variable {G A : Type*} [Group G] [CommGroup A]

/-- A three-group kernel and the actual eight matrix fibers suffice for Q₈ placement. -/
theorem quaternion_le_of_three_kernel_matrix_image
    (f : G →* GL (Fin 2) (ZMod 3) × A) (hker : IsPGroup 3 f.ker)
    (K : Subgroup G)
    (hK : ∀ x : G, ((f x).1.val = 1 ∨ (f x).1.val = -1 ∨
      (f x).1.val ^ 2 = -1) → x ∈ K)
    (P : Subgroup G) (hP : Nonempty (P ≃* QuaternionGroup 2)) : P ≤ K := by
  obtain ⟨e⟩ := hP
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rfl)
  have hi : Function.Injective (f.comp P.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp (hP2.disjoint_of_coprime hker (by decide)) x.property hx
  let g := (f.comp P.subtype).comp e.symm.toMonoidHom
  have hg : Function.Injective g := hi.comp e.symm.injective
  intro x hx
  apply hK x
  simpa only [g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Subgroup.subtype_apply, Subgroup.coe_mk] using
    three_quaternion_prod_image g hg (e ⟨x, hx⟩)
end Matrix.GeneralLinearGroup
