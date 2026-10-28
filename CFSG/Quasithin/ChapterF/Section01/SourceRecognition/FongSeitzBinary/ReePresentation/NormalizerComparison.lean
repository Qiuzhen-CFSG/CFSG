module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceNormalizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.BorelComparison

/-!
# Literal original Cartan squares for the full Ree normalizer comparison

The whole native Cartan lifts through the constructed original common-Borel
isomorphism. Its quotient image agrees with the new full-normalizer comparison,
and both endpoint inclusions preserve that same image. The marking e may come
from the original or universal/geometric quotient; the direct quotient adapter
uses exactly Q.q on the original overlap.

This is the common-intersection compatibility needed to assemble B and N in
the full presentation. It does not assert a comparison of the whole group or
either complete parabolic; the signed-root collection obligation remains.
Source: DGS, *Groups and Graphs*, Theorem D, p.224; Aschbacher--Smith F.1.1--3,
pp.259--261; GLS3 2.3.4--5.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {m : ℕ} (d : SourcePositive.Charts Q split m) (E : SourceAngular.Equations Q split d)
  (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)

/-- Lift every native Cartan element through the original whole common Borel. -/
def originalCartanLift : ReeF4.Parabolics.fixedTorus m →* commonBorel L S :=
  (originalBorelEquiv Q e h split d E T).symm.toMonoidHom.comp
    (inclusion (ReeF4.Parabolics.fixedTorus_le_borel m))

theorem originalCartanLift_injective : Function.Injective (originalCartanLift Q e h split d E T) :=
  (originalBorelEquiv Q e h split d E T).symm.injective.comp (inclusion_injective _)

/-- The source normalizer and original common-Borel markings agree on every
Cartan element, for either original or universal/geometric marking e. -/
theorem originalCartanLift_square (t : ReeF4.Parabolics.fixedTorus m) :
    MarkedLocal.borelMap Q e h (originalCartanLift Q e h split d E T t) =
      (SourceNormalizer.comparison Q split d T W
        ⟨t,ReeF4.SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ : X ⧸ Q.D) := by
  rw [SourceNormalizer.comparison_borel Q split d T W E t]
  have he := originalBorelEquiv_square Q e h split d E T
    (originalCartanLift Q e h split d E T t)
  change (SourceBorel.comparison Q split d E T
    ((originalBorelEquiv Q e h split d E T)
      ((originalBorelEquiv Q e h split d E T).symm _)) : X ⧸ Q.D) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Both literal original endpoint squares commute on the full Cartan. -/
theorem originalCartanLift_endpoint (t : ReeF4.Parabolics.fixedTorus m) (i : Fin 2) :
    MarkedLocal.endpointMap Q e i
      ⟨originalCartanLift Q e h split d E T t,
        commonBorel_le_parabolic i (originalCartanLift Q e h split d E T t).property⟩ =
      (SourceNormalizer.comparison Q split d T W
        ⟨t,ReeF4.SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ : X ⧸ Q.D) := by
  rw [MarkedLocal.endpoint_borel Q e h, originalCartanLift_square Q e h split d E T W]

/-- The literal quotient version uses exactly the same q = X → X/D. -/
def quotientCartanLift : ReeF4.Parabolics.fixedTorus m →* (P 0 ⊓ P 1 : Subgroup X) :=
  (quotientBorelEquiv Q split d E T).symm.toMonoidHom.comp
    (inclusion (ReeF4.Parabolics.fixedTorus_le_borel m))

theorem quotientCartanLift_square (t : ReeF4.Parabolics.fixedTorus m) :
    Q.q (quotientCartanLift Q split d E T t) =
      (SourceNormalizer.comparison Q split d T W
        ⟨t,ReeF4.SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ : X ⧸ Q.D) := by
  rw [SourceNormalizer.comparison_borel Q split d T W E t]
  have he := quotientBorelEquiv_square Q split d E T (quotientCartanLift Q split d E T t)
  change (SourceBorel.comparison Q split d E T
    ((quotientBorelEquiv Q split d E T)
      ((quotientBorelEquiv Q split d E T).symm _)) : X ⧸ Q.D) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  exact he.symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
