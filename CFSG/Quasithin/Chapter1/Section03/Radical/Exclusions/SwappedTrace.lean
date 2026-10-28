module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.InvariantFactor

/-!
# The odd trace of a swapped block factor

The actual plane isomorphism eliminates the extraspecial quotient alternative,
so Φ(P) is trivial. The disjoint conjugate factorization in 1.3.4 then makes
P ∩ K nontrivial and proper. Thus a permuted factor pair whose first trace
is P ∩ K contradicts the N_L(P)-irreducibility proved by the structure task.

The block proof must still construct the pair and establish that trace equality.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- In the swapped case the actual complement has trivial Frattini subgroup. -/
theorem BinaryBlockEmbedding.complement_frattini {p : ℕ} {T X P H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) : frattini P = ⊥ := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  let _ : Fact (IsPGroup p P) := ⟨h.local_input.odd_complement.isPGroup⟩
  have hc : Nat.card P = p ^ 2 :=
    (Nat.card_congr h.plane.some.toEquiv).trans (plane_card p)
  rcases h.local_input.odd_complement with ⟨he, _⟩ | ⟨_, he, _⟩
  · let _ := he
    exact frattini_eq_bot_of_isElementaryAbelian (p := p)
  · have hh := Nat.pow_lt_pow_right h.local_input.prime.one_lt (show 2 < 3 by decide)
    omega

/-- The conjugate intersections in 1.3.4(1) are nontrivial and proper in P. -/
theorem BinaryBlockEmbedding.complement_intersection {p : ℕ} {T X P H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) :
    P ⊓ K ≠ ⊥ ∧ ¬ P ≤ K := by
  have hP : P ≠ ⊥ := by
    intro he
    apply h.local_input.complement_not_cyclic
    rw [he]
    infer_instance
  obtain ⟨t, ht, _, hgen, hd, _⟩ := h.swapped.2
  have htP : P.conjBy t = P := mem_normalizer_iff_map_conj_eq.mp ht.2
  constructor
  · intro he
    have hb : (P ⊓ K).conjBy t = ⊥ := by
      change (P ⊓ K).map _ = ⊥
      rw [he, Subgroup.map_bot]
    exact hP (hgen.trans (by rw [hb, he, bot_sup_eq]))
  · intro hPK
    have he : P ⊓ K = P := inf_eq_left.mpr hPK
    rw [he, htP] at hd
    exact hP (disjoint_self.mp hd)

/-- Identifying the trace of the center-enlarged block factor with P ∩ K
supplies both nontriviality and properness for the final contradiction. -/
theorem BinaryBlockEmbedding.no_factor_pair {p : ℕ} {T X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) (hc : Configuration p T X P L₀ M)
    (A B : Subgroup G)
    (hpair : ∀ d ∈ L₀, A.conjBy d = A ∨ A.conjBy d = B)
    (htrace : P ⊓ A = P ⊓ K) : False := by
  apply hc.no_invariant_factor_pair A B hpair
  · intro hPA
    exact h.complement_intersection.2 (by
      have he : P ⊓ K = P := htrace.symm.trans (inf_eq_left.mpr hPA)
      exact he.symm.le.trans inf_le_right)
  · rw [h.complement_frattini, Subgroup.map_bot, htrace]
    exact fun he => h.complement_intersection.1 (bot_unique he)

end CFSG.Quasithin.Chapter1.RadicalExclusions
