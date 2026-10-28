module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inner
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers

/-!
# Applying odd Sylow transfer to the inner triality bound

The proved two-group center theorem supplies the center hypothesis in the
literal component reduction for every binary triality cover, including q = 2.
The independent absolute displacement bound remains explicit. The earlier
conditional applications of local Sylow geometry remain available.

Source: Guralnick--Malle II §8, internal p.53 and Lemma 8.6; the central
cover calculation is the triality entry of GLS3 §6.1.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality

universe u v
open PerfectCentralCovering.OddSylow

/-- The unconditional central-cover calculation discharges the center premise.
Only the independent absolute displacement estimate on the genuine model remains. -/
theorem componentInvolutionBound_of_model_absoluteBound {R : Type u} [Group R]
    [Finite R] [Theory.GroupTheory.IsQuasisimple R] (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n)
      (R ⧸ Subgroup.center R))
    (hbound : _root_.Triality.InnerDisplacement.AbsoluteBound.{0, v}
      (_root_.Triality.Standard.BinaryCarrier n hn) (5 * n)) :
    ComponentInvolutionBound.{u, v} R n :=
  componentInvolutionBound_of_twoGroup_center n hn hmodel
    (_root_.Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup n hn hmodel) hbound

/-- The local transfer calculation discharges the center premise of the
existing component reduction, while retaining the independent model bound. -/
theorem componentInvolutionBound_of_cover_geometry {R : Type u} [Group R]
    [Finite R] [Theory.GroupTheory.IsQuasisimple R] (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n)
      (R ⧸ Subgroup.center R))
    (hthree : Geometry 3 (_root_.Triality.Standard.BinaryCarrier n hn))
    (hquadratic : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      p ∣ (2 ^ n) ^ 2 - 1 → Geometry p (_root_.Triality.Standard.BinaryCarrier n hn))
    (hother : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ¬ p ∣ (2 ^ n) ^ 2 - 1 → p ∣ Nat.card (_root_.Triality.Standard.BinaryCarrier n hn) →
      Geometry p (_root_.Triality.Standard.BinaryCarrier n hn))
    (hbound : _root_.Triality.InnerDisplacement.AbsoluteBound.{0, v}
      (_root_.Triality.Standard.BinaryCarrier n hn) (5 * n)) :
    ComponentInvolutionBound.{u, v} R n := by
  exact componentInvolutionBound_of_twoGroup_center n hn hmodel
    (_root_.Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup_of_prime_branches
      n hn hmodel hthree hquadratic hother) hbound

/-- In the smallest parameter the checked prime-thirteen exclusion leaves
only the actual three- and seven-primary geometries besides the model bound. -/
theorem componentInvolutionBound_at_two_of_three_seven_geometry
    {R : Type u} [Group R] [Finite R] [Theory.GroupTheory.IsQuasisimple R]
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt 2 (R ⧸ Subgroup.center R))
    (hthree : Geometry 3 (_root_.Triality.Standard.BinaryCarrier 1 (by decide)))
    (hseven : Geometry 7 (_root_.Triality.Standard.BinaryCarrier 1 (by decide)))
    (hbound : _root_.Triality.InnerDisplacement.AbsoluteBound.{0, v}
      (_root_.Triality.Standard.BinaryCarrier 1 (by decide)) 5) :
    ComponentInvolutionBound.{u, v} R 1 := by
  exact componentInvolutionBound_of_twoGroup_center 1 (by decide) (by simpa using hmodel)
    (_root_.Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup_at_two_of_three_seven_geometry
      hmodel hthree hseven) (by simpa using hbound)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
