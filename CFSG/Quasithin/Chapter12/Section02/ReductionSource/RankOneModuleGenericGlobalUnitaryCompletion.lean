module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# Full unitary extension completion inputs in the original Chapter 12 setup

The actual chosen-module input has W equal to the whole reduced module. Its
ordinary or degree-two comparison yields the strict unitary exponent m > 1,
while the full normalizer realization yields a completion with the exact
overlap and the inherited order bound. The PSU₅ branch keeps parameter 4 and
the projective scalar quotient.

These adapters prepare the inputs of F.4.24; recognition and GlobalExit remain
unproved here. The DGS realization and ambient order bound are supplied by
the generic-global source producer. Source: Aschbacher–Smith 5.3.1–4,
F.4.24 and the Chapter 12 application, printed pp.658–659, 287 and795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original whole-reduced-module row supplies the completion inputs
without replacing its exponent n by the unitary exponent m. -/
theorem rankOne_unitary_completion_input (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier ∧
        ∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
            (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_completion_input hi hH hp m hm hc E he horder

/-- The fixed PSU₅(4) realization is a completion on the same original
normalizer pair, without any extra ambient-generation hypothesis. -/
theorem rankOne_unitaryFive_completion_input
    (U : ChapterF.GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)
    (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier :=
  five_normalizer_completion L H U E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
