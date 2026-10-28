module
public import CFSG.Quasithin.Chapter14.Section02.SourceSetup
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic

/-!
# The original outside minimal parabolics of14.2.2(8)

The actual Sylow normalizer lies in M by the plane source. Every minimal
outside H is consequently a genuine minimal parabolic. The intrinsic
restriction retains H intersection M as its unique maximal Sylow overgroup.
Original even characteristic and proper-local inheritance supply SQTK and
F*(H)=O₂(H); original14.2.3 puts H inside the same C_G(Z).

These are the actual inputs to B.6.8 and E.2.2 in14.2.7 and14.2.20. Their
classification conclusions are separate earlier-source theorems.
Source: Aschbacher--Smith14.2.2(8),14.2.3, printed pp.981--982.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_lemma_14_2_2_8_minimal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterB.IsMinimalParabolicOver T H ∧
      ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ ∧
      IsCoatom ((H ⊓ M).subgroupOf H) ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧ generalizedFitting H = pCore 2 H ∧
      H ≤ centralizer (centralInvolutions T : Set G) := by
  have hP := Chapter3.HStar.minimalParabolic T hM.1.2 hH (Or.inl
    ((source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e).trans inf_le_left))
  obtain ⟨hTI,hIH,_⟩ := Chapter3.HStar.unique_maximal T hM.1.2 hH
  obtain ⟨hPi,hmax⟩ := ChapterB.intrinsic_minimalParabolic T H (H ⊓ M) hP hTI hIH
  exact ⟨hP,hPi,hmax,Chapter3.sqtk_of_mem_H hG hH.1.1.1,
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1)),
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2⟩

end CFSG.Quasithin.Chapter14.Section02
