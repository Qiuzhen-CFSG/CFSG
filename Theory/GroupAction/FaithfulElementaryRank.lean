module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Nat.Log
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Quotient

/-!
# Rank of a faithful elementary actor

The literal conjugation homomorphism embeds an elementary binary actor in
the automorphism group of the normalized subgroup. Its rank is therefore
bounded by that automorphism group's two-rank. Only relative normalization
is required.

Source application: Aschbacher--Smith 13.1.9, printed p.871, the bound on
m(A) for the surviving small quotients.
-/

public section
namespace Subgroup
variable {Q : Type*} [Group Q] [Finite Q]
/-- A faithful elementary binary actor embeds in the automorphism group. -/
theorem actor_rank_le_automorphism_rank (K A : Subgroup Q)
    (hAK : A ≤ normalizer (K : Set Q))
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (he : IsElementaryAbelian 2 A) :
    Nat.log 2 (Nat.card A) ≤ primeRank 2 (MulAut K) := by
  let f := K.normalizerMonoidHom.comp (inclusion hAK)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    have hc : (a:Q) ∈ centralizer (K : Set Q) := by
      have hk : inclusion hAK a ∈ K.normalizerMonoidHom.ker := ha
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    exact mem_bot.mp (hf ▸ (show (a:Q) ∈ A ⊓ centralizer (K : Set Q) from ⟨a.property,hc⟩))
  let := he
  have hfe : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hh := (primeRank_le_iff_elementary_card_le (MulAut K)).mp le_rfl f.range hfe
  have hcard : Nat.card A ≤ 2 ^ primeRank 2 (MulAut K) :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).le.trans hh
  have hr := Nat.log_mono_right (b := 2) hcard
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hr
end Subgroup
