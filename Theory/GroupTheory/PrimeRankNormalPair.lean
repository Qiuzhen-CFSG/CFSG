module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.QuotientIntersection
/-!
# Odd ranks of mutually normalizing subgroups

Quotienting by the common two-group makes the two factors commute with
trivial intersection. Odd prime rank is unchanged by that quotient, so
their ranks add. This is the group-theoretic step in Aschbacher–Smith
13.3.14(b), applied to the original residual and its plane conjugate.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem primeRank_add_le_of_normalizes_of_twoGroup_intersection {p : ℕ} [Fact p.Prime] (ho : Odd p) (A B : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G))
    (hI : IsPGroup 2 (A ⊓ B : Subgroup G)) :
    primeRank p A + primeRank p B ≤ primeRank p (A ⊔ B : Subgroup G) := by
  let J := A ⊔ B
  let P := A.subgroupOf J
  let Q := B.subgroupOf J
  let R := P ⊓ Q
  have hPQ : P ≤ normalizer (Q : Set J) := by
    apply le_normalizer_iff.mpr
    intro a ha b hb
    exact le_normalizer_iff.mp hAB a.val ha b.val hb
  have hQP : Q ≤ normalizer (P : Set J) := by
    apply le_normalizer_iff.mpr
    intro b hb a ha
    exact le_normalizer_iff.mp hBA b.val hb a.val ha
  have hJR : ⊤ ≤ normalizer (R : Set J) := by
    rw [← (codisjoint_subgroupOf_sup A B).eq_top]
    exact sup_le
      ((le_inf P.le_normalizer hPQ).trans inf_normalizer_le_normalizer_inf)
      ((le_inf hQP Q.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  let : R.Normal := normalizer_eq_top_iff.mp (top_unique hJR)
  have hRP : R = (A ⊓ B : Subgroup G).subgroupOf J := rfl
  have hR2 : IsPGroup 2 R := hRP ▸ hI.comap_subtype
  let q := QuotientGroup.mk' R
  let Ap := P.map q
  let Bp := Q.map q
  have hker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact hR2
  have hcomm : Ap ≤ centralizer (Bp : Set (J ⧸ R)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hQP)
      (le_normalizer_iff_commutator_le_right.mp hPQ)
  have hdis : Ap ⊓ Bp = ⊥ := by
    rw [← map_inf_of_ker_le q P Q (by
      rw [QuotientGroup.ker_mk']
      exact inf_le_right)]
    change R.map q = ⊥
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  have hr := Theory.GroupTheory.ResidualCentralizerRank.primeRank_add_le_of_coprime_intersection
    (p := p) Ap Bp hcomm (by rw [hdis, Nat.card_unique]; exact Nat.coprime_one_right p)
  have hA : primeRank p Ap = primeRank p A := by
    rw [Theory.GroupTheory.ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hker,
      primeRank_congr p (subgroupOfEquivOfLe (show A ≤ J from le_sup_left))]
  have hB : primeRank p Bp = primeRank p B := by
    rw [Theory.GroupTheory.ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hker,
      primeRank_congr p (subgroupOfEquivOfLe (show B ≤ J from le_sup_right))]
  rw [hA,hB,primeRank_quotient_eq_of_isTwoGroup p ho R hR2] at hr
  exact hr
end Theory.GroupTheory
