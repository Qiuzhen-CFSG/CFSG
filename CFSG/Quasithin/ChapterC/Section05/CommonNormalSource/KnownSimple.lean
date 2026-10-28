module
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource.Original
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.KnownSimpleSource
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.NormalizedCubicComplete

/-!
# C.5.8 over the complete known-simple catalogue

The original outside-block source and the normalized-cubic classification
are now instantiated by their proved known-simple exporters. All natural,
alternating and two-block reductions keep their literal source subgroups.
The common-normal conclusion therefore retains only the genuine earlier
A.3.12 embedding implication, which is not asserted in this module.

Source: Aschbacher–Smith C.5.8–13, printed pp.160–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original C.5.8 common-normal theorem over the complete known-simple
catalogue, retaining exactly the still-independent A.3.12 source implication. -/
theorem theorem_C_5_8_of_A_3_12
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (P : Sylow 2 G) (H M R : Subgroup G) (hPH : (P : Subgroup G) ≤ H)
    (hf : generalizedFitting H = pCore 2 H)
    (hu : Order.HasUniqueMaximalOver (P.subtype hPH : Subgroup H) ⊤)
    (hRP : R ≤ (P : Subgroup G)) (hPM : (P : Subgroup G) ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (Q : Sylow 2 (R ⊔ (pResidual 2 H).map H.subtype : Subgroup G))
    (hQ : (Q : Subgroup (R ⊔ (pResidual 2 H).map H.subtype : Subgroup G)).map
      (R ⊔ (pResidual 2 H).map H.subtype).subtype = R) :
    ∃ N : Subgroup G, N ≠ ⊥ ∧ N ≤ R ∧ (N.subgroupOf (M ⊔ H)).Normal := by
  have hG6 : ChapterG.Section06.NormalizedCubicSourceInput.{u,u} KnownSimple.IsKnownSimple :=
    ChapterG.Section06.normalizedCubicSourceInput_knownSimple_of_earlier_classification
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      ChapterB.SourceClassification.irreducibleClassification_knownSimple
  exact common_normal_of_original hG BlockAnalysis.c128Outside_knownSimple hA312 hG6
    P H M R hPH hf hu hRP hPM hMR Q hQ

end CFSG.Quasithin.ChapterC.Section05
end
