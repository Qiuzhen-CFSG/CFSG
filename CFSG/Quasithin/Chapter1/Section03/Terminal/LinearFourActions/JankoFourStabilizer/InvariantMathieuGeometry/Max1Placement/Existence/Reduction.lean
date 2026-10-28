module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.ProperJoin
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max4Exclusion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy

/-!
# Reduction of J₄ candidate existence to its maximal Sylow overgroups

The proper-join theorem provides a maximal proper subgroup containing A and
its original Sylow S. A concrete maximal-Sylow cover reduces this subgroup
to the literal ATLAS max1, max2, and max4 carriers. The max4 quotient
comparison excludes that branch by perfectness and order. A separate local
exclusion for the literal max2 carrier leaves max1. Restricting S then gives
every field of a candidate, including its actual max1 isomorphism.

The cover, max2 exclusion, and max4 quotient comparison are independent
unproved inputs here. The proper-join and transport arguments discharge all
other premises; ambient simplicity is not needed.

Source: Aschbacher–Smith A.3.12(17) and its proof by Sylow overgroups,
printed pp.47–48; proof of 1.3.9, p.514. The max1/max2/max4 names refer to
the literal matrix-word subgroups, with provenance in their owning modules.
The quotient list in A.3.12 alone does not prove this cover.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels
open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The precise maximal-Sylow cover used here. Every comparison is an actual
multiplicative equivalence with a specified matrix subgroup. -/
@[expose] def MaximalSylowCover : Prop :=
  ∀ (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model),
    IsCoatom M → S.toSubgroup ≤ M →
    Nonempty (M ≃* certifiedMathieuSubgroup) ∨
      Nonempty (M ≃* sourceSubgroup) ∨ Nonempty (M ≃* max4Subgroup)

/-- The local exclusion needed only for the literal ATLAS max2 carrier.
The component is relative to its join with the supplied Sylow. -/
@[expose] def Max2LocalExclusion : Prop :=
  ∀ (B : Subgroup sourceSubgroup) (T : Sylow 2 sourceSubgroup),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    B ∈ ChapterA.Section03.localCComponents T → False

private theorem local_map_equiv {G H : Type*} [Group G] [Group H] [Finite G]
    {A S : Subgroup G} (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (e : G ≃* H) :
    A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents (S.map e.toMonoidHom) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom

private theorem section_isPSL_map {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (e : G ≃* H) (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2) :
    ClassicalGroup.IsPSL (XiQuotient (A.map e.toMonoidHom)) 4 2 := by
  let f := e.subgroupMap A
  exact hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm

/-- An overgroup containing the original Sylow transports the entire local
L₄(2) configuration to its actual model. -/
theorem exists_local_four_in_model {G H : Type*} [Group G] [Group H] [Finite G]
    (A M : Subgroup G) (S : Sylow 2 G)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hAM : A ≤ M) (hSM : S.toSubgroup ≤ M) (e : M ≃* H) :
    ∃ (B : Subgroup H) (T : Sylow 2 H),
      ClassicalGroup.IsPSL (XiQuotient B) 4 2 ∧
      B ∈ ChapterA.Section03.localCComponents T := by
  let C := A.subgroupOf M
  let T := S.subtype hSM
  let f : C ≃* A := subgroupOfEquivOfLe hAM
  have hC : ClassicalGroup.IsPSL (XiQuotient C) 4 2 :=
    hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f))
  refine ⟨C.map e.toMonoidHom, T.mapSurjective (f := e.toMonoidHom) e.surjective,
    section_isPSL_map C e hC, ?_⟩
  exact local_map_equiv (localCComponents_subgroupOf hlocal hAM hSM) e

/-- Conditional assembly. The three concrete inputs remain obligations;
no simplicity, global order, or additional local witness is assumed. -/
theorem concreteCandidateExistence_of_maximal_cover
    (hcover : MaximalSylowCover) (hmax2 : Max2LocalExclusion)
    (e4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel) :
    ConcreteCandidateExistenceTheorem := by
  intro A S hA hlocal
  obtain ⟨M, hM, hAM, hSM⟩ := exists_maximal_local_overgroup A S hA hlocal
  rcases hcover S M hM hSM with h | h | h
  · obtain ⟨e⟩ := h
    exact ⟨M, mem_candidates_of_sylow_le S hlocal hAM hSM e⟩
  · obtain ⟨e⟩ := h
    obtain ⟨B, T, hB, hT⟩ := @exists_local_four_in_model Janko4.Model sourceSubgroup
      Janko4.modelGroup sourceSubgroup.toGroup Janko4.modelFinite A M S hA hlocal hAM hSM e
    exact (hmax2 B T hB hT).elim
  · obtain ⟨e⟩ := h
    obtain ⟨B, T, hB, hT⟩ := @exists_local_four_in_model Janko4.Model max4Subgroup
      Janko4.modelGroup max4Subgroup.toGroup Janko4.modelFinite A M S hA hlocal hAM hSM e
    exact (@no_local_four_of_symmetricLinear_quotient max4Subgroup
      max4Subgroup.toGroup (inferInstance : Finite max4Subgroup) e4 B T.toSubgroup hB hT).elim

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
