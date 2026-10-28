module

public import Theory.Quasithin.Rank

/-!
# Odd-prime rank in a subgroup with a nontrivial normal 2-subgroup

Such a subgroup is contained in a 2-local of the ambient group, so its
odd-prime ranks are at most two when the ambient group is quasithin.
Equivalently, after descending quasithinness to the subgroup, its nontrivial
normal 2-subgroup makes the whole subgroup a 2-local of itself.

This observation permits local rank obstructions to be transported through
parabolic isomorphisms in rank-two amalgam recognition. It does not require
an isomorphism between the ambient completions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
the final paragraph of the proof of Proposition F.1.12, printed p. 264.
-/

@[expose] public section

namespace Theory.Quasithin

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A nontrivial normal 2-subgroup makes quasithinness a bound on the
odd-prime ranks of the entire group. -/
theorem primeRank_le_two_of_normal_two_subgroup
    (hG : IsQuasithin G) (Q : Subgroup G) [Q.Normal]
    (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) : primeRank p G ≤ 2 := by
  have htop : IsTwoLocal (⊤ : Subgroup G) :=
    ⟨Q, hQ, hQp, Q.normalizer_eq_top.symm⟩
  rw [← primeRank_congr p (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)]
  exact isQuasithin_iff_twoLocal.mp hG ⊤ htop p hp hodd

/-- The bound applies to a parabolic in any finite quasithin completion. -/
theorem primeRank_subgroup_le_two_of_normal_two_subgroup
    (hG : IsQuasithin G) (P : Subgroup G) (Q : Subgroup P) [Q.Normal]
    (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) : primeRank p P ≤ 2 :=
  primeRank_le_two_of_normal_two_subgroup (hG.subgroup P) Q hQ hQp p hp hodd

/-- A model parabolic of odd-prime rank at least three cannot occur in a
quasithin completion if the actual parabolic has a nontrivial normal 2-subgroup.
Only a parabolic group isomorphism is needed. -/
theorem not_quasithin_of_parabolic_rank
    (P : Subgroup G) (Q : Subgroup P) [Q.Normal]
    (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q) (e : P ≃* H)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hrank : 3 ≤ primeRank p H) :
    ¬ IsQuasithin G := by
  intro hG
  have hle := primeRank_subgroup_le_two_of_normal_two_subgroup hG P Q hQ hQp
    p hp hodd
  rw [primeRank_congr p e] at hle
  exact (Nat.not_succ_le_self 2) (hrank.trans hle)

end Theory.Quasithin
