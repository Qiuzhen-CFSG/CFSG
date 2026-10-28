module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FullNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.FourNormalClosure

/-!
# Full-normalizer realization for the original Chapter12 linear row

The unchanged chosen-module input constructs a faithful marked common-normalizer
action and a genuine compatible full-normalizer extension of PSL₃(F), retaining
both endpoints, the whole overlap, field four and both orientations. The actual
completion applications discharge the extension and comparison inputs. Ambient
generation and the Hall-quotient cubic relation remain explicit source obligations;
this module does not claim GlobalExit or ambient recognition.

Source: Aschbacher–Smith 5.3.2 and F.4.49, pp.659,298–299, applied in 12.2,
p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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


/-- Original chosen-module application of the complete maximal linear
full-normalizer realization; no local action or extension is assumed. -/
theorem rankOne_global_linear_full_normalizer_marking :
    m = n ∧ Nonempty (Global.LinearNormalizerMarking L (residual H) (Global.sourceS L H) F) :=
  d.linear_full_normalizer_marking (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

/-- The whole marked extension is constructed from the original source row. -/
theorem rankOne_global_linear_full_normalizer_extension :
    m = n ∧ ∃ E : ChapterF.SourceCompletion.LinearThreeEven.SourceExtension F,
      Nonempty (Global.LinearCompletion.NormalizerComparison L (residual H) E) :=
  d.linear_full_normalizer_extension (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

/-- The original ambient group becomes a completion once its generation is proved. -/
theorem rankOne_global_linear_prepared_completion_input
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤) :
    let a := d.linearNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp F hm hF he hmax
    ∃ c : ChapterF.SourceCompletion.LinearThreeEven.Completion a.extension G,
      c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      c.left.range ⊓ c.right.range = c.middle.range :=
  d.linear_prepared_completion_input (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hgen

/-- The unchanged source cubic witness gives full ambient order for the
constructed extension. Neither a literal order-three product nor an ambient
order bound is assumed; generation and cube membership are still explicit. -/
theorem rankOne_global_linear_prepared_card_eq
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    Nat.card G = Nat.card (d.linearNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hmax).extension.carrier :=
  d.linear_prepared_card_eq (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hgen s t hs ht hsout htout hs2 ht2 hcube

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
