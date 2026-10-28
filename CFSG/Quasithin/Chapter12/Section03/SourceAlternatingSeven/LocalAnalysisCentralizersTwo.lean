module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceMoved
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceCover
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSix

/-!
# The moved A₅ module and assembly of the point-centralizer bounds

The point-two input retains the literal perfect residual, its section
centralizer, and [V,K]. If that centralizer fixes the moved module, it fixes
e times a suitable moved vector, a weight-six point. The weight-six bound
then controls this factor of C_G(e). The proved KTY cover from relative
normality controls the whole centralizer. Component conjugacy extends both bounds to their full
weight classes and supplies exactly the input consumed by `localAnalysis`.

The component-enlargement and B.2.14/B.5 module arguments remain explicit
input contracts. The moved weight-four vector and the actual A₅ quotient
are already proved; no instance of the ambient contracts is asserted here.
Their discharge remains with qt-d-1236-1238-point-centralizers, before
qt-d-1231-local-analysis can use the resulting bounds.
Source: Aschbacher--Smith, 12.3.7--8, printed pp.809--810.
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

/-- The checked 12.3.7 source theorem applies once the weight-six
component analysis supplies the preceding ambient centralizer bound. -/
theorem source_1237_of_sixInput (P : SylowNormalizer.Points E) (B : SixInput P)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    Function.Surjective (E.sourceNormalizerModel structural).permutation ∧
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    P.five = ⁅P.five,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) =
      ⁅V,P.five⁆ ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) ∧
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) := by
  apply P.source_1237_of_weight_six structural escape
  intro z _ hz
  exact E.centralizer_le_of_same_weight z P.six (hz.trans P.six_weight.symm)
    (six_centralizer_le P B structural)

/-- The source conclusion after excluding both proper component enlargements.
All groups and the moved module are fixed by P, rather than supplied freely. -/
structure TwoInput (P : SylowNormalizer.Points E) : Prop where
  normalizes : H P.two ≤ normalizer (P.five : Set G)
  fixes_moved : Y (L := L) P.two ≤ centralizer ((⁅V,P.five⁆ : Subgroup G) : Set G)

/-- The final quotient-centralizer factor fixes an actual weight-six point. -/
theorem two_section_le (P : SylowNormalizer.Points E) (B : TwoInput P)
    (hsix : ∀ v : V, weight (E.coordinates v).toAdd.val = 6 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)) :
    Y (L := L) P.two ≤ normalizer (L : Set G) := by
  obtain ⟨w,hw,_,h6⟩ := P.exists_five_moved_weight_four
  apply le_trans ?_ (hsix (P.two*w) h6)
  intro a ha
  apply mem_centralizer_singleton_iff.mpr
  have he := mem_centralizer_singleton_iff.mp
    (ChapterA.Section04.twoSectionCentralizer_le P.five (H P.two) ha)
  have hwc := (mem_centralizer_iff.mp (B.fixes_moved ha)) (w : G) hw
  change a * ((P.two : G) * (w : G)) = ((P.two : G) * (w : G)) * a
  calc
    _ = (a * (P.two : G)) * (w : G) := by rw [mul_assoc]
    _ = ((P.two : G) * a) * (w : G) := by rw [he]
    _ = (P.two : G) * ((w : G) * a) := by rw [mul_assoc, hwc.symm]
    _ = _ := by rw [mul_assoc]

/-- The original KTY factorization finishes the weight-two point centralizer. -/
theorem two_centralizer_le (P : SylowNormalizer.Points E) (B : TwoInput P)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hsix : ∀ v : V, weight (E.coordinates v).toAdd.val = 6 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)) :
    H P.two ≤ normalizer (L : Set G) := by
  apply (P.two_centralizer_cover B.normalizes).trans
  apply sup_le (sup_le ?_ (S.hypothesis.source_sylow_normalizes structural))
    (two_section_le P B hsix)
  exact ((map_subtype_le _).trans inf_le_left).trans L.le_normalizer

/-- Exact `hpoints` consumer: the two genuine source branches suffice at
any chosen central representatives, and component orbits handle all points. -/
theorem pointCentralizers (P : SylowNormalizer.Points E)
    (B6 : SixInput P) (B2 : TwoInput P)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (v : V) (_hv : v ≠ 1)
    (hw : weight (E.coordinates v).toAdd.val = 2 ∨ weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  have h6 : ∀ w : V, weight (E.coordinates w).toAdd.val = 6 →
      centralizer ({(w : G)} : Set G) ≤ normalizer (L : Set G) :=
    fun w hw => E.centralizer_le_of_same_weight w P.six
      (hw.trans P.six_weight.symm) (six_centralizer_le P B6 structural)
  rcases hw with h | h
  · exact E.centralizer_le_of_same_weight v P.two (h.trans P.two_weight.symm)
      (two_centralizer_le P B2 structural h6)
  · exact h6 v h

/-- Apply the proved conditional bounds to the existing local-analysis API.
The point inputs and the earlier Sylow-normalizer bound must still be produced. -/
def localAnalysis (P : SylowNormalizer.Points E)
    (B6 : SixInput P) (B2 : TwoInput P)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) : S.LocalAnalysis :=
  E.localAnalysis structural hNT (pointCentralizers P B6 B2 structural)

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
