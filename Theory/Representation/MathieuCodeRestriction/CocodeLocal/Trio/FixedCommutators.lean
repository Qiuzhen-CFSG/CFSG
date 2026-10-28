module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Displacement
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Residual
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Planes

/-!
# The two commutator spaces of the standard trio cocode

The intrinsic two-core and the intrinsic solvable residual both fix each
octad and contain all paired translations. Fixing the parts puts their
displacements in the pair space. A paired translation moves one point of a
cross-octad pair and fixes the other, so its displacement is any prescribed
pair within an octad. Thus both commutator spaces equal the nine-dimensional
geometric pair space in the actual even-core/Golay quotient.

Source: Aschbacher–Smith, H.15.6(1), printed p.401. These are the commutator
assertions only; the fixed three-space and its full linear action are separate.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

lemma pairSpace_le_commutator_of_pairedTranslations (H : Subgroup M24)
    (hH : ∀ j v, (pairedTranslation j v).val ∈ H) :
    (⨆ B ∈ standardTrio.parts, supportedPairSpace B) ≤
      subspaceCommutator cocodeRepresentation ⊤ H := by
  apply pairSpace_le_commutator_of_move
  intro B hB x hx y hy _
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨⟨a,u⟩, rfl⟩ := point.surjective x
  obtain ⟨⟨b,v⟩, rfl⟩ := point.surjective y
  have hai : a = i := (point_mem_octad_iff a i u).mp hx
  have hbi : b = i := (point_mem_octad_iff b i v).mp hy
  subst a b
  obtain ⟨j,hji⟩ := exists_ne i
  refine ⟨(pairedTranslation j (u + v)).val, hH _ _, point (j,0), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hji (congrArg Prod.fst (point.injective h)).symm
  · intro h
    exact hji (congrArg Prod.fst (point.injective h)).symm
  · change (pairedTranslation j (u + v)).val.val (point (i,u)) = point (i,v)
    rw [pairedTranslation_point, if_neg (Ne.symm hji)]
    apply congrArg (fun w => point (i,w))
    ext k
    simp [Pi.add_apply, ← add_assoc, CharTwo.add_self_eq_zero]
  · change (pairedTranslation j (u + v)).val.val (point (j,0)) = point (j,0)
    simp [pairedTranslation_point]

/-- The intrinsic standard two-core generates precisely the geometric pair space. -/
lemma standard_pairSpace_eq_twoCore_commutator :
    (⨆ B ∈ standardTrio.parts, supportedPairSpace B) =
      subspaceCommutator cocodeRepresentation ⊤
        ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) := by
  apply le_antisymm
  · apply pairSpace_le_commutator_of_pairedTranslations
    intro j v
    exact Subgroup.mem_map_of_mem _ (pairedTranslation_mem_twoCore j v)
  · apply commutator_le_pairSpace_of_fixes_parts
    rintro _ ⟨g,hg,rfl⟩ B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact standardTwoCore_fixes_octad g hg i

/-- The mapped intrinsic solvable residual has the same cocode commutator space. -/
lemma standard_pairSpace_eq_residual_commutator :
    (⨆ B ∈ standardTrio.parts, supportedPairSpace B) =
      subspaceCommutator cocodeRepresentation ⊤
        ((Subgroup.solvableResidual (trioStabilizer standardTrio)).map
          (trioStabilizer standardTrio).subtype) := by
  apply le_antisymm
  · apply pairSpace_le_commutator_of_pairedTranslations
    intro j v
    exact Subgroup.mem_map_of_mem _ (pairedTranslation_mem_residual j v)
  · apply commutator_le_pairSpace_of_fixes_parts
    rintro _ ⟨g,hg,rfl⟩ B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact standardResidual_fixes_octad g hg i

end
end MathieuCode.TrioCalculation
