module

public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PResidual.CommutatorImage

/-!
# Vanishing of the relative centralizer from local uniqueness

If K normalizes D and W centralizes D, the Three Subgroups Lemma
shows that [K,W] centralizes D. After commutator generation, K therefore
centralizes C_D(L). If this two-subgroup were nontrivial and T normalizes
both D and L, its normalizer would contain LT. Uniqueness of the maximal
two-local over LT puts that normalizer in M, contradicting K≰M.

This uses the actual normalizer consequence of uniqueness; no disjointness
of K and M is assumed.
Source: Aschbacher--Smith, 14.4.7, printed p.1009.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem commutator_centralizes_of_normalizes (K D W : Subgroup G)
    (hKD : K ≤ normalizer (D : Set G)) (hDW : ⁅D, W⁆ = ⊥) :
    ⁅K, W⁆ ≤ centralizer (D : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_comm W D, hDW, commutator_bot_left]
  · apply le_bot_iff.mp
    rw [← hDW]
    exact commutator_mono (le_normalizer_iff_commutator_le_left.mp hKD) le_rfl

theorem relative_centralizer_eq_bot_of_unique (K D L T M : Subgroup G)
    (hD : IsPGroup 2 D) (hKD : K ≤ centralizer (D : Set G))
    (hT : T ≤ normalizer (D : Set G)) (hTL : T ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hKM : ¬ K ≤ M) : D ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have hTN : T ≤ normalizer (D ⊓ centralizer (L : Set G) : Set G) :=
    (le_inf hT (hTL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hLN : L ≤ normalizer (D ⊓ centralizer (L : Set G) : Set G) :=
    (le_centralizer_iff.mp inf_le_right).trans (centralizer_le_normalizer _)
  have hNM := normalizer_le_of_unique_maximalTwoLocal hunique
    (hD.to_le inf_le_left) hne (sup_le hLN hTN)
  exact hKM (hKD.trans ((centralizer_le inf_le_left).trans
    ((centralizer_le_normalizer _).trans hNM)))

theorem residual_centralizer_eq_bot_of_generation (J D W L T M : Subgroup G)
    (hD : IsPGroup 2 D) (hJD : J ≤ normalizer (D : Set G))
    (hDW : ⁅D, W⁆ = ⊥) (hgen : (pResidual 2 J).map J.subtype =
      ⁅(pResidual 2 J).map J.subtype, W⁆)
    (hTJ : T ≤ J) (hTL : T ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hKM : ¬ (pResidual 2 J).map J.subtype ≤ M) :
    D ⊓ centralizer (L : Set G) = ⊥ := by
  apply relative_centralizer_eq_bot_of_unique ((pResidual 2 J).map J.subtype) D L T M hD
    _ (hTJ.trans hJD) hTL hunique hKM
  rw [hgen]
  exact commutator_centralizes_of_normalizes _ D W ((map_subtype_le _).trans hJD) hDW
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
