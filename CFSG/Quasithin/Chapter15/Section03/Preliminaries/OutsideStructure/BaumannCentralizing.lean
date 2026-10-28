module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# The centralizing Baumann alternative

The first branch of 15.3.5 identifies Baum(T) with Baum(C_T(V)) and
controls its characteristic normalizers. The inclusions C_T(V) ≤ R ≤ S ≤ T
then give Baum(R)=Baum(S) by Baumann heredity. Faithful subgroup transport
restricts the characteristic-normalizer generation from G to I.

The two core inclusions must be supplied by the complete alternatives of
15.3.11(5). This result handles the centralizing branch of (10); the other
branch and the Thompson escape conclusion still require assembly.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.11(10), p.1124.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

/-- The first alternative of (10) from the centralizing branch of 15.3.5
and the core containments supplied by either alternative of (5). -/
theorem lemma_15_3_11_10_centralizing (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hBR : ChapterB.baumann (d.T : Subgroup G) =
      ChapterB.baumann ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)))
    (hC : (ChapterB.baumann (d.T : Subgroup G)).characteristicNormalizerClosure ≤ d.M)
    (hCR : (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ≤ d.R)
    (hRS : d.R ≤ d.S) :
    ChapterB.baumann d.R = ChapterB.baumann d.S ∧
      ((ChapterB.baumann d.S).subgroupOf I).characteristicNormalizerClosure.map I.subtype ≤ d.MI I := by
  have hBRle : ChapterB.baumann (d.T : Subgroup G) ≤ d.R := by
    rw [hBR]
    exact inf_le_left.trans hCR
  have heR := ChapterB.lemma_B_2_3_4 (d.T : Subgroup G) d.R hBRle
    (hRS.trans (show d.S ≤ (d.T : Subgroup G) from inf_le_left))
  have heS := ChapterB.lemma_B_2_3_4 (d.T : Subgroup G) d.S (hBRle.trans hRS)
    (show d.S ≤ (d.T : Subgroup G) from inf_le_left)
  refine ⟨heR.symm.trans heS, ?_⟩
  have hBSI : ChapterB.baumann d.S ≤ I :=
    inf_le_left.trans (le_sup_right.trans hI.1.2)
  have hC' : (ChapterB.baumann d.S).characteristicNormalizerClosure ≤ d.M := heS ▸ hC
  have hi := characteristicNormalizerClosure_subgroupOf_le hBSI hC'
  have hm := map_mono (f := I.subtype) hi
  rwa [subgroupOf_map_subtype] at hm
end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
