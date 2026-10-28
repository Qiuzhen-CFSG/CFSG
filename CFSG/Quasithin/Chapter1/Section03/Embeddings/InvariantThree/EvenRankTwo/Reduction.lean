module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Shared reductions for the characteristic-two rank-two sieve

The complement has three-rank exactly two, so it cannot embed in a parabolic
of three-rank at most one. Permutability and coprime orders give the order of
RS. Burnside's proved two-prime theorem makes RS solvable, hence proper in
the quasisimple group Q. These facts prepare the geometric containment step;
no parabolic or Borel containment is assumed or asserted here.

An abelian complement is the elementary plane, since the extraspecial
alternative is nonabelian. For p = 3 the congruence 2^n = 1 modulo 3 is
equivalent to even n. The model-specific arguments must still establish the
abelian and congruence hypotheses.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
variable {S : Sylow 2 Q} {R : Subgroup Q}

/-- The available ambient bound and the noncyclic odd complement force rank two. -/
theorem complement_rank (h : PairInput S R) : primeRank 3 R = 2 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu : primeRank 3 R ≤ 2 := (primeRank_subgroup_le 3 R).trans h.rank.le
  have hl : ¬ primeRank 3 R ≤ 1 := by
    intro hr
    apply h.oddComplement.not_isCyclic
    apply h.oddComplement.isPGroup.isCyclic_of_odd_of_elementary_card_le (by decide)
    intro E he
    let _ := he
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E
  omega

/-- The complement cannot lie in a subgroup of three-rank at most one. -/
theorem not_le_of_rank_le_one (h : PairInput S R) {K : Subgroup Q}
    (hK : primeRank 3 K ≤ 1) : ¬ R ≤ K := by
  intro hRK
  have := (primeRank_mono 3 hRK).trans hK
  rw [complement_rank h] at this
  omega

/-- The small-parabolic obstruction survives any map injective on the complement. -/
theorem not_map_le_of_rank_le_one (h : PairInput S R)
    {G : Type v} [Group G] [Finite G] (f : Q →* G)
    (hf : Function.Injective (f.comp R.subtype)) {K : Subgroup G}
    (hK : primeRank 3 K ≤ 1) : ¬ R.map f ≤ K := by
  intro hRK
  let g : R →* K := (f.comp R.subtype).codRestrict K
    (fun x => hRK (mem_map_of_mem f x.property))
  have hg : Function.Injective g := fun _ _ he => hf (congrArg Subtype.val he)
  have := (Theory.GroupTheory.primeRank_le_of_injective 3 g hg).trans hK
  rw [complement_rank h] at this
  omega

/-- Abelianness excludes the extraspecial alternative and supplies actual plane coordinates. -/
theorem complement_plane_of_commutative (h : PairInput S R)
    (hc : IsMulCommutative R) : Nonempty (R ≃* Plane 3) := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := hc
  rcases h.oddComplement with ⟨he, hcard⟩ | ⟨he, _, _⟩
  · let _ := he
    exact plane_of_elementary_card hcard
  · exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
      (center_eq_top (G := R))).elim

omit [Finite Q] in
/-- The odd complement and the Sylow two-subgroup have trivial intersection. -/
theorem complement_disjoint_sylow (h : PairInput S R) :
    Disjoint R (S : Subgroup Q) := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact h.oddComplement.isPGroup.disjoint_of_coprime S.isPGroup' (by decide)

/-- Permutability makes the join have product order; no normalization is assumed. -/
theorem product_card (h : PairInput S R) :
    Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q) = Nat.card R * Nat.card S := by
  have hc := card_set_mul_mul_card_inf R (S : Subgroup Q)
  rw [(complement_disjoint_sylow h).eq_bot, card_bot, mul_one,
    ← coe_sup_of_set_mul_comm R (S : Subgroup Q) h.permutes] at hc
  exact hc

/-- Only two and three divide the order of the actual join RS. -/
theorem product_prime_divisors (h : PairInput S R) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q)) :
    p = 2 ∨ p = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [product_card h] at hd
  rcases hp.dvd_mul.mp hd with hr | hs
  · obtain ⟨n, hn⟩ := h.oddComplement.isPGroup.exists_card_eq
    rw [hn] at hr
    exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow hr) |>.resolve_left
      hp.ne_one)
  · obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn] at hs
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hs) |>.resolve_left
      hp.ne_one)

/-- The genuine product subgroup RS is solvable by the two-prime theorem. -/
theorem product_solvable (h : PairInput S R) :
    Group.IsSolvable (R ⊔ (S : Subgroup Q) : Subgroup Q) :=
  isSolvable_of_prime_dvd_card_eq_two_or_three _
    (fun _ hp hd => product_prime_divisors h hp hd)

/-- The solvable product RS is proper in the quasisimple group. -/
theorem product_ne_top (h : PairInput S R) : R ⊔ (S : Subgroup Q) ≠ ⊤ := by
  intro ht
  let _ := h.quasisimple
  let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let _ : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  let _ : Group.IsSolvable (⊤ : Subgroup Q) := ht ▸ product_solvable h
  exact Group.IsPerfect.not_isSolvable Q (Group.isSolvable_of_surjective
    (f := (topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom) topEquiv.surjective)

/-- At the prime three, the torus congruence gives precisely even field degree. -/
theorem two_pow_modEq_one_iff_even (n : ℕ) : Nat.ModEq 3 (2 ^ n) 1 ↔ Even n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Nat.ModEq]
  | one => norm_num [Nat.ModEq]
  | more n ih _ =>
    have hm : 2 ^ (n + 1 + 1) % 3 = 2 ^ n % 3 := by
      rw [Nat.add_assoc, pow_add]
      norm_num [Nat.mul_mod]
    change (2 ^ (n + 1 + 1) % 3 = 1 % 3 ↔ Even (n + 1 + 1))
    rw [hm]
    simpa [Nat.ModEq, Nat.even_add] using ih

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
