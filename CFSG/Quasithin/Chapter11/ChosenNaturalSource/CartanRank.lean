module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankNormalDetection

/-!
# The Cartan odd-prime obstruction in the chosen natural case

Work inside the join of the Cartan subgroup and its normalized, disjoint
subgroup. If the latter has order divisible by p, the rank-two disjoint-action
theorem forces the Cartan subgroup to have p-rank at most one. Quasithinness
supplies the rank bound on this join through its actual two-local overgroup.

This proves the numerical step of 11.5.6(1), conditional on the geometric
normalization, disjointness and Cartan rank inputs. It does not construct the
line normalizer or its relative component.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.5.6(1), printed p.780, using A.1.27.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource
variable {G : Type*} [Group G] [Finite G]

/-- Rank two in the Cartan subgroup excludes p from a disjoint normalized
subgroup in the same two-local. Ambient normality is not required. -/
theorem cartan_coprime_in_local
    (hG : IsQuasithin G) (H X Y : Subgroup G) (hH : IsTwoLocal H)
    (hX : X ≤ H) (hY : Y ≤ H) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : 2 ≤ primeRank p X) (hn : X ≤ normalizer (Y : Set G))
    (hd : Disjoint X Y) : Nat.Coprime p (Nat.card Y) := by
  let J := X ⊔ Y
  let X' := X.subgroupOf J
  let Y' := Y.subgroupOf J
  let : Y'.Normal := normal_subgroupOf_of_le_normalizer (sup_le hn Y.le_normalizer)
  have hbound : primeRank p J ≤ 2 :=
    (primeRank_le_of_injective p (inclusion (sup_le hX hY))
      (inclusion_injective _)).trans ((isQuasithin_iff_twoLocal.mp hG H hH) p Fact.out ho)
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdiv
  have hdiv' : p ∣ Nat.card Y' := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show Y ≤ J from le_sup_right)).toEquiv]
  have hone := primeRank_le_one_of_disjoint_normal hbound Y' X' hdiv' (by
    intro E hE _
    apply disjoint_def.mpr
    intro x hxE hxY
    apply Subtype.ext
    exact disjoint_def.mp hd (hE hxE) hxY)
  have hlow : 2 ≤ primeRank p X' := by
    let e := subgroupOfEquivOfLe (show X ≤ J from le_sup_left)
    exact hr.trans (primeRank_le_of_injective p e.symm.toMonoidHom e.symm.injective)
  omega

/-- All primes dividing q - 1 are excluded simultaneously, as in 11.5.6(1). -/
theorem cartan_coprime_field_predecessor
    (hG : IsQuasithin G) (H X Y : Subgroup G) (hH : IsTwoLocal H)
    (hX : X ≤ H) (hY : Y ≤ H) {q : ℕ} (hq : Odd (q - 1))
    (hr : ∀ p : ℕ, p.Prime → p ∣ q - 1 → 2 ≤ primeRank p X)
    (hn : X ≤ normalizer (Y : Set G)) (hd : Disjoint X Y) :
    Nat.Coprime (Nat.card Y) (q - 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpY hpq
  let : Fact p.Prime := ⟨hp⟩
  exact (hp.coprime_iff_not_dvd.mp
    (cartan_coprime_in_local hG H X Y hH hX hY (hq.of_dvd_nat hpq)
      (hr p hp hpq) hn hd)) hpY

end CFSG.Quasithin.Chapter11.ChosenNaturalSource
