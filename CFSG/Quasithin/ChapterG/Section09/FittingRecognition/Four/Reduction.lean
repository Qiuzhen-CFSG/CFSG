module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Preparation
public import Theory.Representation.NormalInvariants
public import Theory.Representation.NonsplitFour
public import Theory.GroupTheory.PrimeRankElementary
import Mathlib.Tactic

/-!
# Core orders and actor centralizers in the degree-four branch

The order of GL₄(2) bounds the three-core by nine. The positive actor rank
excludes order one, and rank two excludes order three. A cubic Fitting
commutator intersects every noncubic core trivially, so the actor centralizes
those cores. If the three-core has order three, irreducibility makes each
nonidentity core element fixed-point-free.

These are reductions for the actual input of G.9.4, not a normalizer or
overgroup classification. Source: Aschbacher--Smith, G.9.4, printed p.355.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

private theorem matrix_card :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- The order of the actual three-core divides nine. -/
theorem threeCore_card_dvd_nine (hfaithful : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4) : Nat.card (pCore 3 G) ∣ 9 := by
  have hG := Representation.card_dvd_card_GL_of_injective ρ hfaithful
  rw [hd, matrix_card] at hG
  obtain ⟨n, hn⟩ := (show IsPGroup 3 (pCore 3 G) from pCore_isPGroup).exists_card_eq
  have hdiv : 3 ^ n ∣ 20160 := hn ▸ (pCore 3 G).card_subgroup_dvd_card.trans hG
  have hle : n ≤ 2 := by
    by_contra hn2
    have hbad : 27 ∣ 20160 := (pow_dvd_pow 3 (by omega : 3 ≤ n)).trans hdiv
    norm_num at hbad
  rw [hn]
  exact pow_dvd_pow 3 hle

/-- Positivity of the actor excludes a trivial three-core. -/
theorem threeCore_card_cases (h : Setup ρ A m) (hm : 0 < m)
    (data : ThreeCoreData ρ A m) (hd : Module.finrank (ZMod 2) V = 4) :
    Nat.card (pCore 3 G) = 3 ∨ Nat.card (pCore 3 G) = 9 := by
  have hc := threeCore_card_dvd_nine h.faithful hd
  have hmem := Nat.mem_divisors.mpr ⟨hc, (by decide : 9 ≠ 0)⟩
  rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hone | hthree | hnine
  · have hr : primeRank 3 (pCore 3 G) ≤ 0 := by
      apply (primeRank_le_iff_elementary_card_le _).mpr
      intro E _
      simpa only [hone, pow_zero] using E.card_le_card_group
    have := data.core_rank_ge
    omega
  · exact Or.inl hthree
  · exact Or.inr hnine

/-- At actor rank two the three-core has order exactly nine. -/
theorem threeCore_card_nine_of_rank_two (h : Setup ρ A 2)
    (data : ThreeCoreData ρ A 2) (hd : Module.finrank (ZMod 2) V = 4) :
    Nat.card (pCore 3 G) = 9 := by
  rcases threeCore_card_cases h (by decide) data hd with hc | hc
  · have hr : primeRank 3 (pCore 3 G) ≤ 1 := by
      apply (primeRank_le_iff_elementary_card_le _).mpr
      intro E _
      simpa only [hc, pow_one] using E.card_le_card_group
    have := data.core_rank_ge
    omega
  · exact hc

/-- The noncubic cores are centralized by the actual actor, as used in the
cyclic-three overgroup argument on printed p.355. -/
theorem centralizes_primeCore_of_cubic_commutator
    (hcubic : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 3) :
    A ≤ Subgroup.centralizer (pCore p G : Set G) := by
  have hc3 : IsPGroup 3 (⁅pCore p G, A⁆ : Subgroup G) :=
    hcubic.to_le (Subgroup.commutator_mono (pCore_le_fitting G p) le_rfl)
  have hcp : IsPGroup p (⁅pCore p G, A⁆ : Subgroup G) :=
    (show IsPGroup p (pCore p G) from pCore_isPGroup).to_le
      (Subgroup.commutator_le_left _ _)
  have hbot : ⁅pCore p G, A⁆ = ⊥ :=
    disjoint_self.mp (hcp.disjoint_of_coprime hc3
      ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_three).mpr hp))
  rw [Subgroup.commutator_comm] at hbot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
/-- Every nonidentity element of an order-three core acts without nonzero
fixed vectors. This supplies the hypothesis of the cyclic normalizer calculation. -/
theorem threeCore_fixed_free_of_card_three {K : GroupClass.{u}}
    (h : FittingHypothesis K ρ A m) (hc : Nat.card (pCore 3 G) = 3)
    (b : pCore 3 G) (hb : b ≠ 1) (v : V) (hv : ρ (b : G) v = v) : v = 0 := by
  let : Representation.IsIrreducible ρ := h.irreducible
  have hz : Representation.invariants (ρ.comp (pCore 3 G).subtype) = ⊥ := by
    by_contra hn
    have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ (pCore 3 G) hn
    have he : (b : G) = 1 := h.faithful ((hk b.property).trans ρ.map_one.symm)
    exact hb (Subtype.ext he)
  have hvinv : v ∈ Representation.invariants (ρ.comp (pCore 3 G).subtype) := by
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
      (ρ := ρ.comp (pCore 3 G).subtype) (g := b)
      (fun _ => mem_zpowers_of_prime_card hc hb) v]
    exact hv
  simpa only [hz, Submodule.mem_bot] using hvinv

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
