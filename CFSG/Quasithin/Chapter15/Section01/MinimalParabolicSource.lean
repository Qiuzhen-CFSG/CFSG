module

public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic

/-!
# The actual minimal parabolics in the centralizing branch

The source Baumann control puts the full Sylow normalizer inside M.
Consequently every minimal member of H(T) outside M is a genuine minimal
parabolic, with its original intersection H ∩ M as unique maximal Sylow
overgroup. Restriction preserves the original Sylow subgroup. The ambient
simple QTKE hypotheses supply SQTK and F*(H) = O₂(H).

This is the input to B.6.8 and the nonsolvable E.2.2 analysis in source
15.1.9(7). The proof does not require the module already to have one of
the seven action types in 15.1.7.

Source: Aschbacher--Smith, 3.1.3(2), p.572, and 15.1.9(7), pp.1088--1089.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal parabolic and its exact marked maximal subgroup in 15.1.9(7). -/
theorem source_centralizing_minimalParabolic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterB.IsMinimalParabolicOver T H ∧
      ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ ∧
      IsCoatom ((H ⊓ M).subgroupOf H) ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧ generalizedFitting H = pCore 2 H := by
  obtain ⟨_, _, _, _, _, _, hNT⟩ := source_centralizing_baumann_control hG T hM hJ
  have hP := Chapter3.HStar.minimalParabolic T hM.1.2 hH (Or.inl hNT)
  obtain ⟨hTI, hIH, _⟩ := Chapter3.HStar.unique_maximal T hM.1.2 hH
  obtain ⟨hPi, hmax⟩ := ChapterB.intrinsic_minimalParabolic T H (H ⊓ M) hP hTI hIH
  exact ⟨hP, hPi, hmax, Chapter3.sqtk_of_mem_H hG hH.1.1.1,
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1))⟩

end CFSG.Quasithin.Chapter15.Section01
