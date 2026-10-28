module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FiveOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSixComparison

/-!
# Elimination of the six-dimensional Cartan comparison

If the escaping cubic fails to normalize the original Thompson subgroup,
apply the left FF alternatives to the actual span of the Sylow omega-center.
The natural row is impossible; the symmetric-five row makes its whole
Borel centralize omega. In the right six-space this contradicts the
already-proved omega-centralizer control of the original residual.
Consequently the right module is always four-dimensional, and the left
natural-row Thompson containment and whole-Borel normalization follow.

The block exclusions and torus argument remain necessary for the local
Cartan classification; the dimension conclusion alone does not restrict n.
Source: Aschbacher–Smith 5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Failure of cubic Thompson normalization forces omega-centralization,
by reselecting the actual omega-span in the universal source Input. -/
theorem LocalA7Configuration.cubic_centralizes_of_not_normalizes_thompson
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X D)
    (hn : ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    D ≤ omegaCentralizer T := by
  have hDB : D ≤ localBorel T L := (d.cubic_le.trans inf_le_left).trans c.left_le
  by_cases hLC : L ≤ omegaCentralizer T
  · exact (hDB.trans inf_le_left).trans hLC
  have hs := h.omega_span_input hLC
  rcases hs.borel_thompson_or_five_section (a.left_thompson_moves hs) with hnat | hfive
  · exact (hn (hDB.trans (le_sup_left.trans hnat.2))).elim
  · exact hDB.trans (hs.borel_fixes_omega_of_five_section (le_conjugateSpanBy _ _) hfive)

/-- The right six-space is impossible, using both Hall conditions and the
original cubic escape from the literal residual normalizer. -/
theorem LocalA7Configuration.not_six
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) : Nat.card (localOmegaModule T K) ≠ 64 := by
  intro hc
  have hn := a.six_cubic_not_normalizes_thompson h hH hgen c d hc
  exact a.six_cubic_not_centralizes h hH hgen d hc
    (a.cubic_centralizes_of_not_normalizes_thompson h c d hn)

/-- The actual right module is four-dimensional at every original degree. -/
theorem LocalA7Configuration.four
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) : Nat.card (localOmegaModule T K) = 16 :=
  a.card.resolve_right (a.not_six h hH hgen c d)

/-- The universal noncentral source inputs now have the four-space and
both original Thompson normalizations, without a centralizing-cubic guard. -/
theorem localCartan_noncentral_four_thompson
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      B ⊔ D ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  have hc := a.four h hH hgen c d
  exact ⟨K,a,hc,a.four_cubic_normalizes_thompson h hH hgen c d hc,
    a.four_left_thompson_natural h hH hgen c d hc⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
