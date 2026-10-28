module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.OddDegree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.LocalCentralizer

/-!
# Odd-degree linear generation for the original chosen module

The original exponent n>1 is retained. When n is odd the prepared comparison
proves S=T, the centralizer bound and exact core, ambient generation by both
original pairs, and one involution class. The actual model amalgam then
has a faithful completion in G with the original whole Borel as intersection.
No ambient-generation, core or centralizer callback remains in these odd-degree
applications. PSL₃ recognition and GlobalExit are still owed by the ambient
assembly, as are the even-degree branches.
Source: Aschbacher–Smith §5.3.7, p.660 and F.4.45–46, p.297, applied in
Chapter12, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- Both original joins generate G, and the original Sylow is the source S. -/
theorem rankOne_global_linear_odd_ambient_generation (hnodd : Odd n) :
    Global.sourceS L H = (T : Subgroup G) ∧
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
    L ⊔ residual H = ⊤ := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_sourceS_eq_sylow_of_odd hi hH hp F hm hF he hmax hnodd,
    d.linear_ambient_generation_of_odd hi hH hp F hm hF he hmax hnodd⟩

/-- The original central involution centralizer has core S and lies in the whole overlap. -/
theorem rankOne_global_linear_odd_involution_centralizer (hnodd : Odd n)
    (z : G) (hz : orderOf z = 2) (hzS : z ∈ centerIn (Global.sourceS L H)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
    (centralizer ({z} : Set G)).pCoreIn 2 = Global.sourceS L H := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_centralizer_le_inter_of_odd hi hH hp F hm hF he hmax hnodd z hz hzS,
    d.linear_centralizer_core_eq_sourceS_of_sourceS_eq_sylow hi hH hp F hm hF he hmax
      (d.linear_sourceS_eq_sylow_of_odd hi hH hp F hm hF he hmax hnodd) z hz hzS⟩

/-- The original ambient group has one conjugacy class of involutions for odd n. -/
theorem rankOne_global_linear_odd_involutions_isConj (hnodd : Odd n)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  d.linear_involutions_isConj_of_odd (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hnodd x y hx hy

/-- The original concrete comparison yields a faithful completion in the actual G. -/
theorem rankOne_global_linear_odd_completion (hnodd : Odd n) :
    (∃ c : RankTwoAmalgam.FaithfulCompletion
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F) (G := G),
      c.left.range = ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ∧
      c.right.range = ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range) ∨
    (∃ c : RankTwoAmalgam.FaithfulCompletion
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse (G := G),
      c.left.range = ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ∧
      c.right.range = ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range) :=
  d.linear_ambient_completion_of_odd (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hnodd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
