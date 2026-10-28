module

public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The SL₂ component survives a cubic central quotient of GL₂

The determinant kernel is the actual SL₂. A scalar in this kernel has square
one, so a central kernel of exponent three intersects it trivially. Its image
is therefore a normal subgroup isomorphic to SL₂, and is a component when the
field has more than three elements.

The consumer is the canonical projection of an odd-characteristic SL₃
involution centralizer, in `PSL3.OddInvolutionFixed.CharacteristicTwo`.
Source: Aschbacher--Smith, A.3.21(a), printed p.55, and the component exclusion
in the proof of 1.1.5(3), printed p.503.
-/

public section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace Matrix.GeneralLinearGroup
variable {F H : Type*} [Field F] [Finite F] [Group H]

/-- The determinant-kernel image is a normal component actually isomorphic
to SL₂; the cubic central kernel does not identify its central involution. -/
theorem exists_sl2_component_of_cubic_central_surjection
    (hlarge : 3 < Nat.card F) (f : GL (Fin 2) F →* H)
    (hf : Function.Surjective f) (hk : f.ker ≤ center (GL (Fin 2) F))
    (hcube : ∀ g ∈ f.ker, g ^ 3 = 1) :
    ∃ K : Subgroup H, K.Normal ∧ IsComponent H K ∧ Nonempty (K ≃* SL(2,F)) := by
  let D := (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker
  have hinj : Function.Injective (f.subgroupMap D) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxf : (x : GL (Fin 2) F) ∈ f.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    obtain ⟨u, hu⟩ := show (x : GL (Fin 2) F) ∈ (GeneralLinearGroup.scalar (Fin 2)).range by
      rw [← center_eq_range_scalar]
      exact hk hxf
    have hu2 : u ^ 2 = 1 := by
      have hd := x.property
      change GeneralLinearGroup.det (x : GL (Fin 2) F) = 1 at hd
      rw [← hu, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
      exact hd
    have hx2 : (x : GL (Fin 2) F) ^ 2 = 1 := by
      rw [← hu, ← map_pow, hu2, map_one]
    have hx1 : (x : GL (Fin 2) F) = 1 := by
      simpa only [pow_succ, hx2, one_mul] using hcube x hxf
    exact Subtype.ext hx1
  let e : D ≃* D.map f :=
    MulEquiv.ofBijective (f.subgroupMap D) ⟨hinj, f.subgroupMap_surjective D⟩
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : IsQuasisimple SL(2,F) := ⟨ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  let c : SL(2,F) ≃* D := SpecialLinearGroup.determinantKernelEquiv (Fin 2) F
  let : IsQuasisimple (D.map f) := IsQuasisimple.of_mulEquiv (c.trans e)
  have hn : (D.map f).Normal := (inferInstance : D.Normal).map f hf
  exact ⟨D.map f, hn, ⟨hn.isSubnormal, inferInstance⟩, ⟨(c.trans e).symm⟩⟩
end Matrix.GeneralLinearGroup
