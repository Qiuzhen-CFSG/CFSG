module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Odd prime rank and perfect central covers

For an odd prime `p`, a finite group of `p`-rank at most one has cyclic
Sylow `p`-subgroups. The transfer argument for perfect central extensions
therefore makes every such extension's kernel prime to `p`. Applying this
to the constructed universal cover gives the Schur-multiplier conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.1.1–I.1.2, printed p.407 (PDF p.418).
-/

namespace PerfectCentralCovering

public section

/-- Odd elementary abelian rank at most one makes the kernel of every finite
perfect central extension prime to the given prime. -/
theorem Cover.not_dvd_card_multiplier_of_odd_of_elementary_card_le
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover H G) (hp : Odd p)
    (hE : ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E ≤ p) :
    ¬ p ∣ Nat.card (multiplier f) :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow
    (fun P => P.isCyclic_of_odd_of_elementary_card_le hp hE)

/-- Odd prime rank at most one makes the kernel of every finite perfect
central extension prime to the given prime. -/
theorem Cover.not_dvd_card_multiplier_of_odd_of_primeRank_le_one
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover H G) (hp : Odd p)
    (hr : primeRank p G ≤ 1) :
    ¬ p ∣ Nat.card (multiplier f) :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow
    (fun P => P.isCyclic_of_odd_of_primeRank_le_one hp hr)

/-- The Schur multiplier, realized as the kernel of the concrete universal
perfect central cover. -/
abbrev schurMultiplier (G : Type*) [Group G] [Group.IsPerfect G] :
    Subgroup (UniversalGroup G) := multiplier (universalCover G)

/-- The Schur multiplier of a finite perfect group of odd prime rank at most
one has order prime to that prime. -/
theorem not_dvd_card_schurMultiplier_of_odd_of_primeRank_le_one
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : primeRank p G ≤ 1) :
    ¬ p ∣ Nat.card (schurMultiplier G) :=
  (universalCover G).not_dvd_card_multiplier_of_odd_of_primeRank_le_one hp hr

end

end PerfectCentralCovering
