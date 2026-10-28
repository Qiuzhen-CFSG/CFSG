module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwo
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersSix
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceConclusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisCentralizersTwo at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwo`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace PointCentralizers

theorem source_1237_of_sixInput_at (P : SylowNormalizer.Points E) (B : SixInput P)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    Function.Surjective (E.sourceNormalizerModel_at structural).permutation ∧
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    P.five = ⁅P.five,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) =
      ⁅V,P.five⁆ ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) ∧
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) := by
  apply P.source_1237_of_weight_six_at structural escape
  intro z _ hz
  exact E.centralizer_le_of_same_weight z P.six (hz.trans P.six_weight.symm)
    (six_centralizer_le_at P B structural)

theorem two_centralizer_le_at (P : SylowNormalizer.Points E) (B : TwoInput P)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hsix : ∀ v : V, weight (E.coordinates v).toAdd.val = 6 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)) :
    H P.two ≤ normalizer (L : Set G) := by
  apply (P.two_centralizer_cover B.normalizes).trans
  apply sup_le (sup_le ?_ (S.hypothesis.source_sylow_normalizes_at structural))
    (two_section_le P B hsix)
  exact ((map_subtype_le _).trans inf_le_left).trans L.le_normalizer

theorem pointCentralizers_at (P : SylowNormalizer.Points E)
    (B6 : SixInput P) (B2 : TwoInput P)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (v : V) (_hv : v ≠ 1)
    (hw : weight (E.coordinates v).toAdd.val = 2 ∨ weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  have h6 : ∀ w : V, weight (E.coordinates w).toAdd.val = 6 →
      centralizer ({(w : G)} : Set G) ≤ normalizer (L : Set G) :=
    fun w hw => E.centralizer_le_of_same_weight w P.six
      (hw.trans P.six_weight.symm) (six_centralizer_le_at P B6 structural)
  rcases hw with h | h
  · exact E.centralizer_le_of_same_weight v P.two (h.trans P.two_weight.symm)
      (two_centralizer_le_at P B2 structural h6)
  · exact h6 v h

def localAnalysis_at (P : SylowNormalizer.Points E)
    (B6 : SixInput P) (B2 : TwoInput P)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) : S.LocalAnalysis :=
  E.localAnalysis_at structural hNT (pointCentralizers_at P B6 B2 structural)

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

