module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryAssembly

/-!
# The exact small-component inputs for the original source

The actual parabolic marking separates the binary linear, alternating-six
and binary G₂ rows. The binary quotient and its small-distance module
exclusions are internal. In the other two rows the whole-core block output
supplies quotient simplicity and feeds the already proved marked module
contradiction. Thus no independent quotient-simplicity premise is needed.

Source: Aschbacher–Smith15.3.31, printed p.1132; C.1.32 and C.1.34.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
  SmallExtension.CentralCover.LinearThree ChapterC
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The exact nonbinary whole-core outputs and the binary large-distance
contradiction suffice at the original pair. No universal MS classification,
extra simplicity hypothesis, or pure-center formula is needed. -/
theorem source_small_false_of_core_branches
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (hA6 : ∀ (_ : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) Parabolics.symplecticDerivedParabolic),
      IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ IsAlternatingBlock c.L 6)
    (hG2 : ∀ (_ : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Atlas.G2.Model (ZMod 2))) Parabolics.g2DerivedParabolic),
      IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock c.L)
    (hlarge : ∀ (_ : Parabolics.RankTwoParabolicMarking d I c.L SL Parabolics.linearThreeParabolic)
      (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
      (t : BinaryMS.MS93.InputSetup (source_binaryMSInput s e)),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf I)) →
      4 < t.geometry.b t.reduction.radical → False) : False := by
  cases hm with
  | linearThree m => exact source_linearThree_false_of_large_distance s m (hlarge m)
  | symplecticDerived m =>
    have hc : MarkedMS.CoreAlternatives c.L d.S := Or.inl (hA6 m)
    exact source_small_false_of_MS_cases s (.symplecticDerived m) (Or.inl (hA6 m))
      (MarkedMS.coreAlternatives_simple c.core_quotient_quasisimple hc)
  | g2Derived m =>
    have hc : MarkedMS.CoreAlternatives c.L d.S := Or.inr (Or.inl (hG2 m))
    exact source_small_false_of_MS_cases s (.g2Derived m) (Or.inr (Or.inl (hG2 m)))
      (MarkedMS.coreAlternatives_simple c.core_quotient_quasisimple hc)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
