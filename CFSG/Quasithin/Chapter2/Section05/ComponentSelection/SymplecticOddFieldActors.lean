module
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Exclusion
public import Theory.GroupAction.ComponentRankAction

/-!
# Odd split-prime actors on the original symplectic component quotient

The actual split torus supplies rank two in the marked central quotient.
The p-prime central kernel lifts that rank to the original perfect subgroup.
Its normalizer action therefore has rank at most two and contains all inner
automorphisms. The complete symplectic field-actor exclusion now applies to
this literal action image, with no field-decomposition or fixed-rank premise.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, in the proof of 2.5.7,
printed p.556. Component normality and residual transport remain with the
Chapter 2 assembly owner.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {p n : ℕ} [Fact p.Prime]

theorem symplectic_action_range_inner
    (hF : Nat.card F = 2^n) (hn : 1 < n) (ho : Odd p) (hd : p ∣ 2^n-1)
    (L : Subgroup H) [Group.IsPerfect L] (e : L ⧸ center L ≃* Sp F)
    (hZ : Nat.Coprime p (Nat.card (center L))) (hH : primeRank p H ≤ 2)
    (a : MulAut (Sp F)) (ha : a ∈ (action L e).range)
    (hpow : ∃ m : ℕ, a ^ (p^m) = 1) : a ∈ MulAut.innerSubgroup (Sp F) := by
  have hdF : p ∣ Nat.card F-1 := hF ▸ hd
  have hL : 2 ≤ primeRank p L := by
    have hr := OddFieldActors.split_prime_rank hdF
    rw [← primeRank_equiv p e] at hr
    exact hr.trans (primeRank_le_of_surjective_of_coprime p (QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective _) (by simpa only [QuotientGroup.ker_mk'] using hZ))
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact OddFieldActors.primePower_actor_inner hlarge ho hdF (action L e).range
    (inner_le_range L e) (range_rank_le_two L e hZ hL hH) a ha hpow

theorem symplectic_normalizer_primePower_action_inner
    (hF : Nat.card F = 2^n) (hn : 1 < n) (ho : Odd p) (hd : p ∣ 2^n-1)
    (L : Subgroup H) [Group.IsPerfect L] (e : L ⧸ center L ≃* Sp F)
    (hZ : Nat.Coprime p (Nat.card (center L))) (hH : primeRank p H ≤ 2)
    (x : normalizer (L : Set H)) (hx : ∃ m : ℕ, x ^ (p^m) = 1) :
    action L e x ∈ MulAut.innerSubgroup (Sp F) := by
  apply symplectic_action_range_inner hF hn ho hd L e hZ hH _ ⟨x,rfl⟩
  obtain ⟨m,hm⟩ := hx
  exact ⟨m,by rw [← map_pow,hm,map_one]⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
