module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Inner
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion.FiveCensus

/-!
# Native unitary subcompletions for the literal Chapter 12 input

With W equal to the whole reduced module, the prepared comparison gives
m > 1 and n = 2m for U₄, or n = 4 for PSU₅(4). The supplied compatible
full DGS realization retains both original normalizers and their entire
overlap. The normal native subamalgam construction now applies literally.
For U₄ the order bound and ambient simplicity make the native endpoint
images generate G; for U₅ they give a normal native subcompletion of the
original normalizer join, transitive on both full-extension vertex types.
Neither assertion is an identification with PSU or a GlobalExit.

Source: Aschbacher–Smith 5.3.1–4, F.4.17 and Chapter 12,
printed pp.658–659,282–283,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Both ordinary and degree-two U₄ comparison orientations give the actual
native projective amalgam completion in the original simple G. -/
theorem rankOne_unitary_native_ambient_completion (D : ChosenModule T L V)
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
    1 < m ∧ n = 2*m ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      ∃ b : RankTwoAmalgam.FaithfulCompletion
          (SourceExtension.nativeAmalgam
            (P₀ := ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm)
            (P₁ := ChapterF.GreenBook.LieModels.UnitaryFour.planeParabolic m hm)) (G := G),
        b.left = E.innerLeft c ∧ b.right = E.innerRight c ∧
        b.left.range ⊓ b.right.range = b.middle.range := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_native_ambient_completion hi hH hp m hm hc E he horder

/-- The fixed PSU₅(4) branch retains the actual projective kernel and both
normalizer markings in its normal native subcompletion. -/
theorem rankOne_unitaryFive_normal_native_completion (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      (E.innerGenerated c).Normal ∧
      (E.innerCompletion c (five_conj_injective U)).left.range ⊓
        (E.innerCompletion c (five_conj_injective U)).right.range =
        (E.innerCompletion c (five_conj_injective U)).middle.range ∧
      (∀ v : Vertex c.cosetFamily, ∃ a : E.innerGenerated c,
        a.val • base c.cosetFamily v.type = v) ∧
      (∀ v : Vertex (E.innerFamily c),
        Nat.card ((Subgroup.CosetGeometry.RankTwo.graph (E.innerFamily c)).neighborSet v) =
          fiveDegree v.type) ∧
      (E.innerGenerated c).index ∣ E.nativeOverlap.index := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_normal_native_completion hi hH hp U hc E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
