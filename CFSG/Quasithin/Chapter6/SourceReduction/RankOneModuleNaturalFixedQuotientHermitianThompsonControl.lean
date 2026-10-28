module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianThompson
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Original normalizer control of the Hermitian Thompson subgroup

The whole LT normalizes J(T), and J(T) is a nontrivial two-group. Uniqueness
of the original maximal two-local over LT therefore puts its full normalizer
inside M. Every actual subgroup escaping M consequently fails to normalize
J(T), as required before the last source fusion argument.
Source: Aschbacher--Smith Remark 6.1.2 and proof of 6.1.4, printed pp.663,666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The full original Thompson normalizer lies in M in the Hermitian case. -/
theorem original_hermitian_thompson_normalizer_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M := by
  let hi := h.reduced_enlargement.rankOneInput hout
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    have hR : reducedSubgroup (L ⊔ (T : Subgroup G)) = ⊥ :=
      bot_unique (hi.reduced_le_sylow.trans_eq ht)
    exact hi.noncentral (by rw [hR,commutator_bot_left])
  apply normalizer_le_of_unique_maximalTwoLocal
    (J := L ⊔ (T : Subgroup G))
    (fun N hN hLN => (hi.unique_local_join N hN hLN).trans h.maximal_eq_normalizer_L.symm)
    (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup (T : Subgroup G) T.isPGroup' hT)
  exact hi.hermitian_join_normalizes_thompson hm (by decide)

/-- Every actual outside subgroup moves J(T); no normalizer premise is added. -/
theorem original_hermitian_outside_not_normalizes_thompson
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    {K : Subgroup G} (hK : ¬ K ≤ M) :
    ¬ K ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
  fun hn => hK (hn.trans (original_hermitian_thompson_normalizer_le h hout hm))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
