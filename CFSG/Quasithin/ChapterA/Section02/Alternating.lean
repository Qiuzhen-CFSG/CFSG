module

public import Theory.Alternating.OddCentralCovers
public import Theory.SpecificGroups.Alternating.QuasithinBounds
public import CFSG.Quasithin.ChapterA.Section02.Statements

/-!
# Alternating-family elimination for A.2.16

For a nontrivial odd-primary central cover, the Schur multiplier restriction
forces degree six or seven and center order three. The simple quotient then
has 3-rank two, contradicting the earlier-source rank conclusion in A.2.14.
In the simple case the A₄ × A₆ two-local obstruction forces degree at most
nine, and A₉'s 3-rank excludes strong quasithinness. Actual isomorphisms then
place the group in the precise B and C lists. No theorem A, B or C for the
ambient group is assumed.

The proper A₁₀ section is supplied separately for the source's A.2.15 route.
The A.2 assembly owner supplies minimality and the A.2.13–14 reduction; the
cover contradiction below retains its exact earlier-source rank premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma A.2.16, printed p.38 (PDF p.49).
-/

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterA.Section02

open GLS3.Chapter5 GLS3.Chapter5.PRank Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The odd-cover restriction, including the rank of the literal simple quotient. -/
theorem odd_primary_alternating_cover
    [IsQuasisimple G] {n p : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (ho : Odd p)
    (hP : IsPGroup p (Subgroup.center G)) (hZ : Subgroup.center G ≠ ⊥)
    (e : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin n)) :
    p = 3 ∧ (n = 6 ∨ n = 7) ∧ Nat.card (Subgroup.center G) = 3 ∧
      primeRank 3 (G ⧸ Subgroup.center G) = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hzodd : Odd (Nat.card (Subgroup.center G)) := by
    rw [hk]
    exact ho.pow
  have hz1 : Nat.card (Subgroup.center G) ≠ 1 := fun h => hZ ((Subgroup.eq_bot_iff_card _).mpr h)
  obtain ⟨hdeg, hcard⟩ := (OddCentralCovers.odd_center_alternatives n hn e hzodd).resolve_left hz1
  have hpd : p ∣ 3 := hcard ▸ (hP.card_eq_or_dvd.resolve_left hz1)
  have hp3 : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp hpd).resolve_left hp.ne_one
  refine ⟨hp3, hdeg, hcard, ?_⟩
  rw [primeRank_equiv 3 e, alternating_primeRank_of_odd_prime n 3 (by decide) (by decide)]
  rcases hdeg with rfl | rfl <;> rfl

/-- The corresponding exact rank statement for the triple cover itself. -/
theorem odd_alternating_cover_exceptional
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (hcenterP : IsPGroup 3 (Subgroup.center K))
    (hthree : 3 ∣ Nat.card (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    (n = 6 ∨ n = 7) ∧ Nat.card (Subgroup.center K) = 3 ∧ HasPRank K 3 2 := by
  have hdeg := three_dvd_center_forces_exceptional_degree n hn e hthree
  exact ⟨hdeg, three_primary_exceptional_center_card_eq_three n e hdeg hcenterP hthree,
    proposition_5_2_10_c n hn hcenterP hthree e⟩

/-- A₉ has elementary abelian 3-rank three. -/
theorem alternating_A9_hasPRank_three : HasPRank (alternatingGroup (Fin 9)) 3 3 := by
  exact alternating_hasPRank_of_odd_prime 9 3 (by decide) (by decide)

/-- A₁₀ has elementary abelian 3-rank three. -/
theorem alternating_A10_hasPRank_three : HasPRank (alternatingGroup (Fin 10)) 3 3 := by
  exact alternating_hasPRank_of_odd_prime 10 3 (by decide) (by decide)

/-- A₉ has 3-rank three in the invariant used by strong quasithinness. -/
theorem alternating_A9_primeRank_three : primeRank 3 (alternatingGroup (Fin 9)) = 3 :=
  alternating_A9_hasPRank_three.primeRank_eq (by decide)

/-- The A₄ × A₆ construction gives the required two-local 3-rank obstruction. -/
theorem alternating_A10_twoLocal_rank : 3 ≤ twoLocalPrimeRank 3 (alternatingGroup (Fin 10)) :=
  alternatingGroup.three_le_ten_twoLocalPrimeRank

/-- Larger degrees contain a proper A₁₀ section via an actual subgroup embedding. -/
theorem alternating_has_proper_A10 {n : ℕ} (hn : 10 < n)
    (e : G ≃* alternatingGroup (Fin n)) :
    IsProperSectionOf (alternatingGroup (Fin 10)) G := by
  let f := (e.symm.toMonoidHom).comp (alternatingGroup.degreeEmbedding hn.le)
  have hf : Function.Injective f := e.symm.injective.comp
    (alternatingGroup.degreeEmbedding_injective hn.le)
  have hftop : f.range ≠ ⊤ := by
    intro h
    have hsur := MonoidHom.range_eq_top.mp h
    have hsur' : Function.Surjective (alternatingGroup.degreeEmbedding hn.le) := by
      intro y
      obtain ⟨x, hx⟩ := hsur (e.symm y)
      exact ⟨x, e.symm.injective hx⟩
    exact alternatingGroup.degreeEmbedding_range_ne_top (by decide : 2 ≤ 10) hn
      (MonoidHom.range_eq_top.mpr hsur')
  exact (IsProperSectionOf.subgroup f.range hftop).of_mulEquiv (MonoidHom.ofInjective hf)

/-- A quasithin alternating model belongs to B, and to C when strongly quasithin. -/
theorem alternating_simple_models {n : ℕ} (e : G ≃* alternatingGroup (Fin n))
    (hqt : IsQuasithin G) : IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hn := alternatingGroup.degree_le_nine_of_quasithin (isQuasithin_of_equiv e hqt)
  refine ⟨.alternating n hn ⟨e⟩, ?_⟩
  intro hsq
  have hn8 : n ≤ 8 := by
    by_contra h
    have heq : n = 9 := by omega
    subst n
    have hr := hsq 3 (by decide) (by decide)
    rw [primeRank_equiv 3 e, alternating_A9_primeRank_three] at hr
    omega
  exact .alternating n hn8 ⟨e⟩

/-- Case II of A.2.13 is incompatible with the quotient rank conclusion of A.2.14. -/
theorem exclude_odd_alternating_cover [IsQuasisimple G] {n p : ℕ}
    (hn : 5 ≤ n) (hp : p.Prime) (ho : Odd p)
    (hP : IsPGroup p (Subgroup.center G)) (hZ : Subgroup.center G ≠ ⊥)
    (hr : 2 < primeRank p (G ⧸ Subgroup.center G))
    (e : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨rfl, _, _, heq⟩ := odd_primary_alternating_cover hn hp ho hP hZ e
  omega

/-- The simple alternating case is a counterexample to neither B nor C. -/
theorem alternating_theorems_BC {G : Type*} [Group G] [Finite G]
    {K : GroupClass} {n : ℕ} (e : G ≃* alternatingGroup (Fin n)) :
    TheoremB K G ∧ TheoremC K G := by
  constructor
  · intro _ _ hqt _
    exact (alternating_simple_models e hqt).1
  · intro _ _ hsq _
    exact (alternating_simple_models e hsq.quasithin).2 hsq

/-- Apply the simple-case conclusions to the literal central-quotient marking. -/
theorem alternating_centerless_theorems_BC
    {K : GroupClass} {n : ℕ} (hZ : Subgroup.center G = ⊥)
    (e : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin n)) :
    TheoremB K G ∧ TheoremC K G := by
  exact alternating_theorems_BC
    (OddCentralCovers.alternatingEquivOfCenterCardOne n e
      (by rw [hZ, Subgroup.card_bot]))

end CFSG.Quasithin.ChapterA.Section02
