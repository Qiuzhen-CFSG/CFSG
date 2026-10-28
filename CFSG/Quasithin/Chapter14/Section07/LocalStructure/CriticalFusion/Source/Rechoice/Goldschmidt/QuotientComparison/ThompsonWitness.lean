module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.Action
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ComponentSelection

/-!
# Normalizer escape, Thompson exclusion, and the small subnormal witness in 14.7.70

The original natural-module setup constructs the projection of N_G(L) onto
L/O₂(L). Its residual-image calculation and the full E-action give the literal
escape Y ≰ N_G(L). This implies Thompson escape via the relative normality
in 14.3.9(2) and uniqueness of the maximal two-local over LT.

On the original V_I, Thompson escape removes the trivial actor from the
complete adequate B.5.6 alternatives. A solvable alternative supplies an
actual subnormal S₃ in I/O₂(I). In the component alternative, a conjugate of
the lifted C-component moves the original involution, proving its actual
L_f(G,T) membership before applying 14.3.4. Its intrinsic quotient then gives
an actual subnormal L₃(2) or A₅ through the same plus map.

The three source conclusions are assembled below with no local projection,
escape, family-membership or witness premise. The genuine earlier universal
inputs remain explicit: Structural1222 and the full setup contracts belong
to qt-12-02-reduction and the Chapter 1/12 setup owners (including
qt-1-02-adequate-assembly); 14.3.9(2) and 14.3.4(1–2) to qt-14-03-prelim;
the complete adequate B.5.6 contract to qt-b05-general-classification/qt-b-05.
The Goldschmidt source assembly retains their discharge and the construction
of Geometry and CoreFacts. The quotient-comparison parent consumes the
resulting SmallSubnormal in its independent F.6 comparison.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.70, printed pp.1074–1075 (PDF pp.1091–1092).
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
open Chapter12.Section08
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The actual classification application after the source normalizer escape.
The universal source inputs retain their full contracts in Action.lean. -/
theorem thompson_and_adequate_of_escape (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u})
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (escape : ¬ Y c ≤ normalizer (L : Set G)) :
    (¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2) ∧
      (letI := module_elementary d c k
       ChapterB.SourceInduction.NontrivialAdequateAlternative
         ((action d c h k).comp (offenderSubgroup (action d c h k)).subtype)) := by
  have hJ := thompson_not_le_core_of_escape d c earlier thompson escape
  exact ⟨hJ, nontrivial_adequate_alternative d c h k b5 hJ⟩

/-- The literal source escape from N_G(L), using the constructed normalizer
projection and the proved residual-action argument. The only earlier input
is the universal structural implication, applied to the original source data. -/
theorem normalizer_escape (h : Geometry d c) (k : CoreFacts c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ¬ Y c ≤ normalizer (L : Set G) :=
  ProjectionEscape.normalizer_escape d structural h k

/-- The actual ambient Thompson subgroup escapes O₂(I). Literal 14.3.9(2)
and uniqueness over LT apply after the normalizer escape is proved. -/
theorem thompson_not_le_core (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u}) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 :=
  thompson_not_le_core_of_escape d c earlier thompson
    (normalizer_escape d c h k earlier.structural)

/-- The B.5 witness required by the source quotient comparison: a genuine
subnormal S₃, L₃(2), or A₅ in the literal I/O₂(I). The faithful action,
nontrivial adequate alternative, component-family membership, and quotient
transport are all supplied; only the full earlier universal contracts remain. -/
theorem smallSubnormal (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple) :
    SmallSubnormal c := by
  obtain ⟨_, alternative⟩ := thompson_and_adequate_of_escape d c h k earlier thompson b5
    (normalizer_escape d c h k earlier.structural)
  exact ComponentSelection.smallSubnormal_of_adequate d c h k classification alternative

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
