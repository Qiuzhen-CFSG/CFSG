module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceSieveBound
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Complete
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.HeldCenterSource

/-!
# The E.6.3 lower bound with the E.6.23 model recognition discharged

The complete quotient-recognition theorem applies to the original Sylow
subgroup and elementary module in E.6.1. Supplying it to the full-minimum
argument proves the E.6.3 rank bounds without a quotient-recognition premise.
All earlier classification and common-normal inputs are already discharged
by that argument. The only remaining source premise is the E.6.18 exclusion
of the exceptional seven-component case. Its original source producer
then reduces the final E.6.3 consumer to the odd-center theorem for finite
quasisimple Held covers; the hypothesis for that producer follows from m > 2.

Source: Aschbacher–Smith, E.6.3 and E.6.18–25, printed pp.245,252–256.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction

open Hyperplanes Hyperplanes.Enlargement

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

/-- The original E.6.3 conclusions with the E.6.23 model classification
proved, retaining precisely the earlier E.6.18 seven exclusion. -/
theorem lower_bound_knownSimple_of_sevenExcluded [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h18 : SevenExcluded M V) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V :=
  lower_bound_knownSimple_of_hyperplane_models h hm h18
    (SixAutomorphisms.ModelIdentification.quotientRecognition T M V)

/-- E.6.3 on its original ambient group and module, with only the genuine
odd-center theorem for finite quasisimple Held covers left to supply. -/
theorem lower_bound_knownSimple_of_held_center [IsElementaryAbelian 2 V]
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V :=
  lower_bound_knownSimple_of_sevenExcluded h hm
    (Hyperplanes.ComponentBalance.sevenExcluded_of_held_center hHeld h (Or.inr hm))

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
