module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootPlanePresentation.CorootMatrices
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Eliminating the torus part of the F4 plane-completion kernel

The actual rank-one matrix identities make each coroot family multiplicative
in the quotient by the plane relations. The common plane of two simple roots
makes their coroots commute. Their four-parameter product therefore has image
exactly the simple-coroot subgroup of the completion. Evaluation identifies
this product with the faithful diagonal homomorphism proved in `CorootMatrices`.

Consequently evaluation kills no nonidentity element of that subgroup. The
last theorem applies this result to the original all-root kernel equality,
leaving precisely the global normal-form kernel-containment premise explicit.
It does not assert that this premise, or the full presentation, is proved.

Source: Steinberg, *Lectures on Chevalley Groups*, §3, printed pp.40–42,
Lemma 28 and Theorem 8 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
variable (F : Type*) [Field F]

private def completionMatrix : RootPlaneCompletion F →*
    (Matrix (typeF4RootPairing_base.support ⊕ typeF4Roots)
      (typeF4RootPairing_base.support ⊕ typeF4Roots) F)ˣ :=
  (Cover F).subtype.comp (rootCompletionEvaluation F)

private theorem coroot_one (i : Fin 4) : completionCoroot F i 1 = 1 := by
  change rootPlaneQuotient F (rootHWord F (sourceIndex i) 1) = _
  change rootPlaneQuotient F (rootHWord F (sourceIndex i) 1) = rootPlaneQuotient F 1
  apply rootPlaneQuotient_eq_of_plane F (sourceIndex i) (sourceIndex i)
    (rootHWord_mem_plane F _ _ _ (rootPlane_left _ _) _) (Subgroup.one_mem _)
  apply Subtype.ext
  rw [map_one, rootHWord_matrix]
  simp

private theorem coroot_mul (i : Fin 4) (s t : Fˣ) :
    completionCoroot F i (s * t) = completionCoroot F i s * completionCoroot F i t := by
  change rootPlaneQuotient F _ = rootPlaneQuotient F _ * rootPlaneQuotient F _
  rw [← map_mul]
  apply rootPlaneQuotient_eq_of_plane F (sourceIndex i) (sourceIndex i)
    (rootHWord_mem_plane F _ _ _ (rootPlane_left _ _) _)
    (Subgroup.mul_mem _ (rootHWord_mem_plane F _ _ _ (rootPlane_left _ _) _)
      (rootHWord_mem_plane F _ _ _ (rootPlane_left _ _) _))
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul, rootHWord_matrix]
  rw [Pi.mulSingle_mul, map_mul]

/-- Each simple coroot family is multiplicative using its rank-one relations. -/
def completionCorootHom (i : Fin 4) : Fˣ →* RootPlaneCompletion F where
  toFun := completionCoroot F i
  map_one' := by exact coroot_one F i
  map_mul' := by exact coroot_mul F i

/-- Two simple coroot families commute by their common plane relations. -/
theorem completionCoroot_commute (i j : Fin 4) (s t : Fˣ) :
    Commute (completionCoroot F i s) (completionCoroot F j t) := by
  change rootPlaneQuotient F _ * rootPlaneQuotient F _ =
    rootPlaneQuotient F _ * rootPlaneQuotient F _
  simp only [← map_mul]
  apply rootPlaneQuotient_eq_of_plane F (sourceIndex i) (sourceIndex j)
    (Subgroup.mul_mem _ (rootHWord_mem_plane F _ _ _ (rootPlane_left _ _) _)
      (rootHWord_mem_plane F _ _ _ (rootPlane_right _ _) _))
    (Subgroup.mul_mem _ (rootHWord_mem_plane F _ _ _ (rootPlane_right _ _) _)
      (rootHWord_mem_plane F _ _ _ (rootPlane_left _ _) _))
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul, rootHWord_matrix]
  rw [← map_mul, ← map_mul, mul_comm]

private theorem corootHom_commute (i j : Fin 4) (s t : Fˣ) :
    Commute (completionCorootHom F i s) (completionCorootHom F j t) :=
  completionCoroot_commute F i j s t

/-- The four-parameter torus formed from actual coroot words in the completion. -/
def completionTorusHom : (Fin 4 → Fˣ) →* RootPlaneCompletion F :=
  MonoidHom.noncommPiCoprod (completionCorootHom F)
    (by intro i j _ s t; exact corootHom_commute F i j s t)

@[simp] theorem completionTorusHom_single (i : Fin 4) (t : Fˣ) :
    completionTorusHom F (Pi.mulSingle i t) = completionCoroot F i t :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem completionTorusHom_range :
    (completionTorusHom F).range = completionCorootSubgroup F := by
  rw [completionTorusHom, MonoidHom.noncommPiCoprod_range]
  apply le_antisymm
  · apply iSup_le
    intro i
    rintro _ ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨(i, t), rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact (le_iSup (fun j => (completionCorootHom F j).range) i) ⟨t, rfl⟩

private theorem completionTorus_matrix (t : Fin 4 → Fˣ) :
    completionMatrix F (completionTorusHom F t) = rootTorusMatrixHom F t := by
  have he : (completionMatrix F).comp (completionTorusHom F) = rootTorusMatrixHom F := by
    apply MonoidHom.pi_ext
    intro i u
    simp only [MonoidHom.comp_apply, completionTorusHom_single]
    exact rootHWord_matrix F i u
  exact DFunLike.congr_fun he t

/-- No nonidentity element of the simple-coroot subgroup is killed by evaluation. -/
theorem rootCompletionEvaluation_eq_one_of_mem_coroot {g : RootPlaneCompletion F}
    (hg : g ∈ completionCorootSubgroup F) (he : rootCompletionEvaluation F g = 1) :
    g = 1 := by
  rw [← completionTorusHom_range] at hg
  obtain ⟨t, rfl⟩ := hg
  have hm : rootTorusMatrixHom F t = 1 := by
    rw [← completionTorus_matrix]
    exact congrArg Subtype.val he
  have ht := rootTorusMatrixHom_injective F (hm.trans (map_one _).symm)
  rw [ht, map_one]

/-- The actual presentation follows once the normal-form argument has put the
comparison kernel in the four-coroot subgroup. That source premise remains explicit. -/
theorem ker_eq_rootPlaneRelationSubgroup_of_coroot_reduction
    (h : (rootCompletionEvaluation F).ker ≤ completionCorootSubgroup F) :
    (rootEvaluation F).ker = rootPlaneRelationSubgroup F := by
  apply le_antisymm _ (rootPlaneRelationSubgroup_le F)
  intro w hw
  apply (rootPlaneQuotient_eq_one_iff F w).mp
  exact rootCompletionEvaluation_eq_one_of_mem_coroot F (h hw) hw

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
