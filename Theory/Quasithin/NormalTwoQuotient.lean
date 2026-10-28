module
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Odd-prime rank in a normal two-extension

An odd-prime Sylow subgroup has trivial image in the two-group quotient,
so it embeds in the specified normal subgroup. This gives equality of the
odd-prime ranks. Source application: the final SQTK assertion in
Aschbacher–Smith E.2.2, printed pp.215–216.
-/
public section
open Subgroup
variable {H : Type*} [Group H] [Finite H]
theorem primeRank_le_of_normal_two_quotient (N : Subgroup H) [N.Normal]
    (hq : IsPGroup 2 (H ⧸ N)) (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    primeRank p H ≤ primeRank p N := by
  let P : Sylow p H := Classical.choice inferInstance
  let q := QuotientGroup.mk' N
  have hpN : (P : Subgroup H) ≤ N := by
    have hd := (P.isPGroup'.map q).disjoint_of_coprime
      (hq.to_subgroup ((P : Subgroup H).map q)) (Nat.coprime_two_right.mpr ho)
    have he : (P : Subgroup H).map q = ⊥ := by simpa using hd.eq_bot
    simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using he
  rw [P.primeRank_eq]
  exact _root_.primeRank_le_of_injective p (inclusion hpN) (inclusion_injective hpN)


/-- A normal subgroup with two-group quotient has the same odd-prime ranks. -/
theorem primeRank_eq_of_normal_two_quotient (N : Subgroup H) [N.Normal]
    (hq : IsPGroup 2 (H ⧸ N)) (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    primeRank p H = primeRank p N :=
  le_antisymm (primeRank_le_of_normal_two_quotient N hq p ho) (primeRank_subgroup_le p N)
