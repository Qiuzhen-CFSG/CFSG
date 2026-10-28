module

public import Theory.GroupTheory.PerfectCentralCoverRank
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Perfect-cover inputs for I.1.1--I.1.2

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), printed p.407, discusses universal perfect central coverings
and their Schur multipliers. The derived subgroup of the free central extension
provides the finite universal cover; universality gives compatible uniqueness.
At an odd prime, rank at most one forces cyclic Sylow subgroups, and transfer
then shows that every finite perfect central extension has kernel of order
prime to the given prime. In particular, the Schur multiplier has this property.
-/

namespace CFSG.Quasithin.ChapterI

open PerfectCentralCovering

universe u v

/-- Existence in I.1.1: every finite perfect group has a finite universal
perfect central cover, universal for targets in any given universe. -/
public theorem perfectCover_exists
    (G : Type u) [Group G] [Finite G] [Group.IsPerfect G] :
    ∃ (L : Type u) (_ : Group L) (_ : Finite L) (f : Cover L G),
      IsUniversal.{u, u, v} f :=
  ⟨UniversalGroup G, inferInstance, inferInstance, universalCover G,
    universalCover_isUniversal⟩

/-- The uniqueness assertion in I.1.1, given two universal perfect covers. -/
public theorem perfectCovers_unique
    {L M : Type u} {G : Type v} [Group L] [Group M] [Group G]
    [Finite L] [Finite M] [Finite G]
    (f : Cover L G) (g : Cover M G)
    (hf : IsUniversal.{u, v, u} f) (hg : IsUniversal.{u, v, u} g) :
    ∃! e : L ≃* M, g.toMonoidHom.comp e.toMonoidHom = f.toMonoidHom :=
  hf.existsUnique_mulEquiv f g hg

/-- The kernel-control step of I.1.2, for every finite perfect central
extension whose quotient has cyclic Sylow subgroups at the given prime. -/
public theorem perfectCover_kernel_prime_to_of_cyclic_sylow
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover H G)
    (hcyclic : ∀ P : Sylow p G, IsCyclic P) :
    ¬ p ∣ Nat.card (multiplier f) :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow hcyclic

/-- I.1.2 in the stronger form applying to every finite perfect central
extension, not only the universal one. -/
public theorem perfectCover_kernel_prime_to_of_odd_rank_le_one
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover H G)
    (hp : Odd p) (hr : primeRank p G ≤ 1) :
    ¬ p ∣ Nat.card (multiplier f) :=
  f.not_dvd_card_multiplier_of_odd_of_primeRank_le_one hp hr

/-- I.1.2: the Schur multiplier of a finite perfect group of odd prime rank
at most one has order prime to that prime. -/
public theorem schurMultiplier_prime_to_of_odd_rank_le_one
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : primeRank p G ≤ 1) :
    ¬ p ∣ Nat.card (PerfectCentralCovering.schurMultiplier G) :=
  not_dvd_card_schurMultiplier_of_odd_of_primeRank_le_one hp hr

end CFSG.Quasithin.ChapterI
