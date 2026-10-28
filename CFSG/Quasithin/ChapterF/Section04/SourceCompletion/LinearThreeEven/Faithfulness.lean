module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.FullGeometry
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness

/-!
# The full middle has no hidden action kernel

The native Borel core is trivial by simplicity and its properness. The inner
subgroup therefore acts faithfully on the full extension graph. An element
in the kernel of the extended action would conjugate each native inner actor
to itself, forcing that automorphism to be the identity on the native carrier.
Transferring the full marked middle core then proves faithful coset action in
every completion with whole overlap, including all outer factors.

Source: Aschbacher–Smith F.3.3–4 and F.4.3–4, pp.270–274
(`refs/quasithin.pdf`). This is an action-kernel result, not group recognition.
-/

@[expose] public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

theorem native_borel_core : (borel F).normalCore = ⊥ := by
  let _ : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  rcases (inferInstance : (borel F).normalCore.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hb : borel F = ⊤ := top_unique (h ▸ (borel F).normalCore_le)
    exact (reflection_not_mem_borel F false (hb.symm ▸ mem_top _)).elim

theorem native_vertex_action_injective :
    Function.Injective (MulAction.toPermHom PSL(3,F) (Vertex (parabolic F))) := by
  rw [←MonoidHom.ker_eq_bot_iff,global_kernel]
  have hi : parabolic F false ⊓ parabolic F true = borel F := NativePaths.family_inf F false
  rw [hi,native_borel_core]

variable {F} (E : SourceExtension F)

/-- The model extension acts faithfully, including its entire outer part. -/
theorem extension_vertex_action_injective :
    Function.Injective (MulAction.toPermHom E.carrier (Vertex E.family)) := by
  let π := MulAction.toPermHom E.carrier (Vertex E.family)
  have hi : Function.Injective (π.comp E.baseHom) := by
    intro a b h
    apply native_vertex_action_injective F
    apply Equiv.Perm.ext
    intro v
    apply E.vertexMap_injective (native_conj_injective F)
    have hh := Equiv.Perm.ext_iff.mp h (E.vertexMap (native_conj_injective F) v)
    exact (E.vertexMap_smul (native_conj_injective F) a v).trans
      (hh.trans (E.vertexMap_smul (native_conj_injective F) b v).symm)
  apply (MonoidHom.ker_eq_bot_iff π).mp
  apply bot_unique
  intro a ha
  change a=1
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  apply hi
  change π (E.baseHom (a.val x)) = π (E.baseHom x)
  have hc : E.baseHom (a.val x) = a * E.baseHom x * a⁻¹ := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    simp [UnitaryNonbinary.SourceExtension.baseHom]
  rw [hc,map_mul,map_mul,map_inv,show π a=1 from ha]
  simp

/-- The entire model middle has trivial core, not just its native intersection. -/
theorem extension_middle_core :
    (E.completion (parabolics_sup_eq_top F)).middle.range.normalCore = ⊥ := by
  have h := (MonoidHom.ker_eq_bot_iff _).mpr (extension_vertex_action_injective E)
  rw [global_kernel,←E.completion_family (parabolics_sup_eq_top F)] at h
  change ((E.completion (parabolics_sup_eq_top F)).left.range ⊓
    (E.completion (parabolics_sup_eq_top F)).right.range).normalCore = ⊥ at h
  rwa [E.completion_overlap] at h

namespace Completion
variable {E} {G : Type*} [Group G] (c : Completion E G)

/-- No normal subgroup of a completion can hide in its full marked middle. -/
theorem middle_normalCore : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model (E.completion (parabolics_sup_eq_top F)) (extension_middle_core E)

/-- The literal full-normalizer coset action is faithful once overlap is whole. -/
theorem vertex_action_injective (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (MulAction.toPermHom G c.Vertex) := by
  rw [←MonoidHom.ker_eq_bot_iff,global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [ho,c.middle_normalCore]

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
