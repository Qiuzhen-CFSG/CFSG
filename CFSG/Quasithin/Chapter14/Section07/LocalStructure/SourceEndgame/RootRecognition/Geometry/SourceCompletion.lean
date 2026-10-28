module

public import CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Quotient

/-!
# Projective recognition discharged for the actual root quotient

The universal field-four case of G.1.3 supplies the recognition implication
used by the source 14.7.73 quotient. Applying it to the already constructed
action on the literal O₂(K)/E proves the natural-copy decomposition, with
the original qK and quotient kernel. No recognition premise remains.
The source multiplicity argument still determines that there is one copy.

Source: Aschbacher–Smith, G.1.3 and 14.7.73, printed pp.327 and 1076–1077.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
universe u

/-- The universal G.1.3 implication for every finite binary SL₂(4)-module. -/
theorem naturalRecognition : NaturalRecognition.{u} := by
  intro M _ _ _ σ φ h
  exact ChapterG.Section01.SL2FourRecognition.naturalCopies h

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal 14.7.73 quotient has natural coordinates; G.1.3 is proved. -/
theorem quotient_natural_copies (d : Data T L V F W) (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer L) (m : MarkedImages d k) :
    let := intersection_normal d k hS hPhi hTL m
    let := quotient_elementary d k hS hPhi hTL m
    ∃ (σ : Representation (ZMod 2) SL2FourNatural.SL
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2))))
      (_c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k) (σ.comp (qK d)))
      (s : ℕ), NaturalCopies σ s :=
  exists_natural_copies d k hS hPhi hTL m naturalRecognition

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.SourceCompletion
