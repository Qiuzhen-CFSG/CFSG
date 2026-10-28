module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Inputs

/-!
# The core quotient and sixth flag term

The cocode fixed-space marking and coordinate duality give V/V5 the genuine
six-point augmentation action. The preimage of its constant line is V6.
Rank-nullity proves its dimension, and the checked permutation-subspace
classification proves that V6 is maximal invariant.

Source: Aschbacher--Smith H.16.4(1),(3), p.403, manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

namespace CocodeActionData

def quotientCoreEquiv (D : CocodeActionData E) :
    (M22Code ⧸ V5.toSubmodule) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6) :=
  ((quotientDualEquiv U.toSubmodule).trans D.fixedEquiv.symm.dualMap).trans
    (coreDeletedDualEquiv (Fin 6)).symm

theorem quotientCoreEquiv_equivariant (D : CocodeActionData E) (g : Stabilizer)
    (v : M22Code ⧸ V5.toSubmodule) :
    D.quotientCoreEquiv (V5.quotientRepresentation g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (D.quotientMap g)
        (D.quotientCoreEquiv v) := by
  have hm (w : M22Code ⧸ V5.toSubmodule) :
      coreDeletedDualEquiv (Fin 6) (D.quotientCoreEquiv w) =
        D.fixedEquiv.symm.dualMap (quotientDualEquiv U.toSubmodule w) :=
    (coreDeletedDualEquiv (Fin 6)).apply_symm_apply _
  apply (coreDeletedDualEquiv (Fin 6)).injective
  calc
    _ = D.fixedEquiv.symm.dualMap
        (quotientDualEquiv U.toSubmodule (V5.quotientRepresentation g v)) := hm _
    _ = D.fixedEquiv.symm.dualMap (U.toRepresentation.dual g
        (quotientDualEquiv U.toSubmodule v)) :=
      congrArg D.fixedEquiv.symm.dualMap (quotientDualEquiv_equivariant Stabilizer U g v)
    _ = (BinaryPermutation.deletedRepresentation (Fin 6)).dual (D.quotientMap g)
        (D.fixedEquiv.symm.dualMap (quotientDualEquiv U.toSubmodule v)) :=
      dual_equivariant U.toRepresentation (BinaryPermutation.deletedRepresentation (Fin 6))
        D.quotientMap D.fixedEquiv D.fixedEquiv_equivariant g _
    _ = (BinaryPermutation.deletedRepresentation (Fin 6)).dual (D.quotientMap g)
        (coreDeletedDualEquiv (Fin 6) (D.quotientCoreEquiv v)) :=
      congrArg ((BinaryPermutation.deletedRepresentation (Fin 6)).dual (D.quotientMap g))
        (hm v).symm
    _ = _ := (coreDeletedDualEquiv_equivariant (Fin 6) (D.quotientMap g)
      (D.quotientCoreEquiv v)).symm

def coreProjection (D : CocodeActionData E) :
    M22Code →ₗ[ZMod 2] BinaryPermutation.core (Fin 6) :=
  D.quotientCoreEquiv.toLinearMap.comp V5.toSubmodule.mkQ

theorem coreProjection_surjective (D : CocodeActionData E) :
    Function.Surjective D.coreProjection :=
  D.quotientCoreEquiv.surjective.comp V5.toSubmodule.mkQ_surjective

theorem coreProjection_ker (D : CocodeActionData E) :
    D.coreProjection.ker = V5.toSubmodule := by
  ext v
  change D.quotientCoreEquiv (V5.toSubmodule.mkQ v) = 0 ↔ v ∈ V5.toSubmodule
  rw [D.quotientCoreEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem coreProjection_equivariant (D : CocodeActionData E) (g : Stabilizer) (v : M22Code) :
    D.coreProjection (codeAction g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (D.quotientMap g) (D.coreProjection v) :=
  D.quotientCoreEquiv_equivariant g (V5.toSubmodule.mkQ v)

end CocodeActionData

/-- The literal constant line inside the six-point augmentation core. -/
def coreConstants : Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)) :=
  (BinaryPermutation.constants (Fin 6)).comap (BinaryPermutation.core (Fin 6)).subtype

theorem coreConstants_finrank : Module.finrank (ZMod 2) coreConstants = 1 := by
  rw [show coreConstants = (BinaryPermutation.constants (Fin 6)).comap
    (BinaryPermutation.core (Fin 6)).subtype from rfl,
    (Submodule.comapSubtypeEquivOfLe
      ((BinaryPermutation.constants_le_core_iff (Fin 6)).mpr (by decide))).finrank_eq]
  exact BinaryPermutation.finrank_constants (Fin 6)

namespace CocodeActionData

/-- V6 is the inverse image of the constant line in the genuine core quotient. -/
def codeSix (D : CocodeActionData E) : Subrepresentation codeAction where
  toSubmodule := coreConstants.comap D.coreProjection
  apply_mem_toSubmodule g v hv := by
    change D.coreProjection (codeAction g v) ∈ coreConstants
    rw [D.coreProjection_equivariant]
    exact BinaryPermutation.constants_invariant (Fin 6) (D.quotientMap g) hv

theorem five_le_six (D : CocodeActionData E) : V5 ≤ D.codeSix := by
  intro v hv
  change D.coreProjection v ∈ coreConstants
  have hz : D.coreProjection v = 0 := by
    change v ∈ D.coreProjection.ker
    rwa [D.coreProjection_ker]
  rw [hz]
  exact coreConstants.zero_mem

theorem coreProjection_map_six (D : CocodeActionData E) :
    D.codeSix.toSubmodule.map D.coreProjection = coreConstants :=
  Submodule.map_comap_eq_of_surjective D.coreProjection_surjective _

theorem codeSix_finrank (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) D.codeSix.toSubmodule = 6 := by
  have he := HexadTransfer.finrank_map_add_ker D.coreProjection D.codeSix.toSubmodule
    (by rw [D.coreProjection_ker]; exact D.five_le_six)
  rw [D.coreProjection_map_six, coreConstants_finrank, D.coreProjection_ker,
    codeCommutatorSubrepresentation_finrank h h24] at he
  exact he.symm

theorem code_strict (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    (⊥ : Subrepresentation codeAction) < V1 ∧ V1 < V5 ∧ V5 < D.codeSix ∧ D.codeSix < ⊤ := by
  have h5 : Module.finrank (ZMod 2) V5.toSubmodule = 5 :=
    codeCommutatorSubrepresentation_finrank h h24
  have h6 := D.codeSix_finrank h h24
  have hp := code_prefix_strict h h24
  refine ⟨hp.1, ?_, ?_, ?_⟩
  · change V1.toSubmodule < V5.toSubmodule
    rw [codeCommutatorSubrepresentation_space]
    exact hp.2.1
  · apply lt_of_le_of_ne D.five_le_six
    intro he
    rw [he] at h5
    omega
  · apply lt_top_iff_ne_top.mpr
    intro he
    rw [he] at h6
    change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) M22Code) = 6 at h6
    rw [finrank_top, finrank_m22Code] at h6
    omega

/-- The checked permutation-module classification transfers through the actual
quotient marking: there are exactly three invariant spaces above V5. -/
theorem above_five_classification (D : CocodeActionData E)
    (P : Subrepresentation codeAction) (hP : V5 ≤ P) :
    P = V5 ∨ P = D.codeSix ∨ P = ⊤ := by
  let W := (P.toSubmodule.map D.coreProjection).map
    (BinaryPermutation.core (Fin 6)).subtype
  have hW : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ W,
      BinaryPermutation.representation (Fin 6) g.val v ∈ W := by
    rintro g _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := D.quotientMap_surjective g.val
    refine ⟨D.coreProjection (codeAction a v), ⟨codeAction a v,
      P.apply_mem_toSubmodule a hv, rfl⟩, ?_⟩
    rw [D.coreProjection_equivariant, ha]
    rfl
  have hback : (W.comap (BinaryPermutation.core (Fin 6)).subtype).comap
      D.coreProjection = P.toSubmodule := by
    dsimp [W]
    rw [Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _),
      Submodule.comap_map_eq, D.coreProjection_ker]
    exact sup_eq_left.mpr (show V5.toSubmodule ≤ P.toSubmodule from hP)
  rcases BinaryPermutation.invariant_submodule_classification
    (by decide : 5 ≤ Fintype.card (Fin 6)) W hW with hw | hw | hw | hw
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hback, hw, Submodule.comap_bot, Submodule.ker_subtype,
      Submodule.comap_bot, D.coreProjection_ker]
  · right; left
    apply Subrepresentation.toSubmodule_injective
    rw [← hback, hw]
    rfl
  · right; right
    apply Subrepresentation.toSubmodule_injective
    rw [← hback, hw, Submodule.comap_subtype_self, Submodule.comap_top]
    rfl
  · have hl : W ≤ BinaryPermutation.core (Fin 6) := Submodule.map_subtype_le _ _
    rw [hw] at hl
    exact ((BinaryPermutation.core_lt_top (Fin 6)).not_ge hl).elim

theorem codeSix_covBy_top (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    D.codeSix ⋖ (⊤ : Subrepresentation codeAction) := by
  refine ⟨(D.code_strict h h24).2.2.2, ?_⟩
  intro P hSP hPT
  rcases D.above_five_classification P (D.five_le_six.trans hSP.le) with hp | hp | hp
  · subst P
    exact (not_lt_of_ge D.five_le_six) hSP
  · subst P
    exact lt_irrefl _ hSP
  · subst P
    exact lt_irrefl _ hPT

end CocodeActionData
end MathieuCode.Hexad.ChiefFlag.Actions
