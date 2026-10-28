module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.MathieuEleven
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.MathieuTwelve
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.MathieuRemaining
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.JankoTwoHigmanSims
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.JankoFour.Source
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.Held
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.Rudvalis
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction

/-!
# The complete sporadic source inspection in 15.3.43

The original action quotient receives the faithfully embedded normal
four-group. Nine sporadic models contradict its local geometry directly;
for M₁₂ the residual centralizer is trivial, contradicting the retained
nontrivial first-plane action. The dispatcher uses exactly the ten carriers
in 1.1.5(3)(f), preserving the source quotient L/O₂(L).

Every concrete model input is discharged by its imported producer. The final
consumer constructs the reduced configuration from the literal earlier
source inputs. Those earlier inputs remain with the full source assembly.

Source: Aschbacher--Smith, 1.1.5(3)(f), printed p.502, and 15.3.43, p.1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G] {Y S M I L V₁ V₂ : Subgroup G}

/-- All ten sporadic cases of 1.1.5(3)(f) are incompatible with the
original rank-one reduced configuration. -/
theorem reduced_not_listed_image (c : ReducedConfiguration Y S M I L V₁ V₂)
    (hm : IsListedModel (c.toComponentAction.image L)) : False := by
  obtain ⟨name, hn, ⟨e⟩⟩ := hm
  let q := localConfiguration_of_reduced c
  cases name with
  | m11 => exact q.not_mathieu_eleven e
  | m12 => exact reduced_image_centralizer_ne_bot c (q.mathieu_twelve_centralizer e)
  | m22 => exact q.not_mathieu_twentyTwo e
  | m23 => exact q.not_mathieu_twentyThree e
  | m24 => exact q.not_mathieu_twentyFour e
  | j2 => exact q.not_janko_two e
  | j3 => exact hn rfl
  | j4 => exact reduced_not_janko_four c e
  | hs => exact q.not_higman_sims e
  | he => exact q.not_held e
  | ru => exact q.not_rudvalis e

/-- The literal quotient convention of the source's sporadic list. -/
theorem reduced_not_listed_two_core_quotient (c : ReducedConfiguration Y S M I L V₁ V₂)
    (hm : IsListedModel (L ⧸ pCore 2 L)) : False :=
  reduced_not_listed_image c (listed_image_of_two_core_quotient c hm)

/-- Actual 15.3.43 source application, retaining all earlier source inputs. -/
theorem source_not_symmetricThreeShadow_of_sporadic_model
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    (hm : IsListedModel (L ⧸ pCore 2 L)) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact reduced_not_listed_two_core_quotient
    (reducedConfiguration_of_source d hI h hshadow halt) hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
