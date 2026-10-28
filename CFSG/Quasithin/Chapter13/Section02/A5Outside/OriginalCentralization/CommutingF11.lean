module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalF11
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreTwoFiftySixExclusion
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BaumannBlocks
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockCore

/-!
# F.1.1 directly from an original commuting pair

The actual commuting pair has both whole two-cores of order at least512.
Its omega-center has order at most four; order two would force an original
alternating block with core sixteen. Thus the omega-center has order four,
and the original fixed lines give the literal F.1.1 hypothesis.

This local implication uses the actual two Contexts and whole local action.
It does not use the earlier5.2.3 classifier or a catalogue exclusion.
Source: Aschbacher--Smith 13.2.8(1), p.880, and C.1.24(a).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The original commuting branch supplies F.1.1 before any application
of the earlier classifier. -/
theorem original_commuting_pair_hypothesisF11
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G)) :
    Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      ChapterF.Source.HypothesisF11 ![L,K] (T : Subgroup G) := by
  have hbound := (original_pair_omega_bounds d e hH hjoin hJd hJe).1
  have hdiv : 2 ∣ Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := by
    simpa only [d.flag.one_card] using
      (card_dvd_of_le (le_sup_left.trans (omega_decomposition_of_thompson_moves d hJd).ge) :
        Nat.card V₁ ∣ Nat.card (omegaOneCenterAmbient (T : Subgroup G)))
  have hpos : 0 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := Nat.card_pos
  have hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
    by_contra hn
    have hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by omega
    have hcards := original_commuting_pair_core_cards_ge_fiveTwelve d e hjoin hH
      (d.localActor_surjective_of_thompson_moves hJd) q hq hk he hVW
    rcases original_pair_block_of_omega_card_two d e hjoin hH hJd hJe hz with hb | hb
    · have hc := d.block_local_core_card_of_omega_card_two hb hz
      omega
    · have hc := e.block_local_core_card_of_omega_card_two hb hz
      rw [hjoin] at hc
      omega
  exact ⟨hfour,original_pair_hypothesisF11 d e hjoin hH hJd hJe hfour⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
