module

public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PrimeRankZero

/-!
# Rank bounds for the action on a perfect central quotient

If a subgroup has full p-rank and p-prime center, its centralizer has order
prime to p: the commuting rank-addition inequality leaves that centralizer
rank zero. The normalizer's action on any marked central quotient has exactly
this centralizer as kernel, since the subgroup is perfect. The literal action
image therefore retains the ambient rank bound and contains every inner actor.

Source: Aschbacher--Smith, A.3.18, printed pp.51--53, in the proof of 2.5.7,
p.556. The component/model hypotheses used to obtain full p-rank are separate
from this elementary action calculation.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Theory.GroupAction.ComponentRankAction

variable {G S : Type*} [Group G] [Group S]

/-- The original normalizer acts on the supplied central-quotient coordinates. -/
def action (L : Subgroup G) (e : L ⧸ center L ≃* S) :
    normalizer (L : Set G) →* MulAut S :=
  (MulAut.centralQuotientAction e).comp L.normalizerMonoidHom

/-- On a component element this is its inner action, with the original quotient map. -/
theorem action_on_component (L : Subgroup G) (e : L ⧸ center L ≃* S) (x : L) :
    action L e ⟨x, L.le_normalizer x.property⟩ =
      MulAut.conj (e (QuotientGroup.mk' (center L) x)) := by
  have hx : L.normalizerMonoidHom ⟨x, L.le_normalizer x.property⟩ = MulAut.conj x := by
    ext y
    rfl
  change MulAut.centralQuotientAction e (L.normalizerMonoidHom _) = _
  rw [hx, MulAut.centralQuotientAction_conj]

/-- Surjectivity of the marked central quotient supplies the full inner image. -/
theorem inner_le_range (L : Subgroup G) (e : L ⧸ center L ≃* S) :
    MulAut.innerSubgroup S ≤ (action L e).range := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨x, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center L))) s
  exact ⟨⟨x, L.le_normalizer x.property⟩, action_on_component L e x⟩

/-- Perfectness retains the exact ordinary centralizer as action kernel. -/
theorem ker_eq (L : Subgroup G) [Group.IsPerfect L] (e : L ⧸ center L ≃* S) :
    (action L e).ker = (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
  rw [action, MonoidHom.ker_comp_of_injective _ _ (MulAut.centralQuotientAction_injective e),
    normalizerMonoidHom_ker]

variable [Finite G] {p : ℕ} [Fact p.Prime]

/-- A full-rank subgroup with p-prime center has p-prime centralizer. -/
theorem centralizer_coprime (L : Subgroup G)
    (hZ : Nat.Coprime p (Nat.card (center L)))
    (hL : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card (centralizer (L : Set G))) := by
  have hr := GroupTheory.ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (centralizer (L : Set G)) L le_rfl hZ
  have hz : primeRank p (centralizer (L : Set G)) = 0 := by omega
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)

/-- The kernel of the actual normalizer action is p-prime, including central covers. -/
theorem kernel_coprime (L : Subgroup G) [Group.IsPerfect L] (e : L ⧸ center L ≃* S)
    (hZ : Nat.Coprime p (Nat.card (center L)))
    (hL : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card (action L e).ker) := by
  rw [ker_eq, Nat.card_congr
    (subgroupOfEquivOfLe (centralizer_le_normalizer (L : Set G))).toEquiv]
  exact centralizer_coprime L hZ hL hG

/-- Coprime kernel lifting proves the rank bound on this same action image. -/
theorem range_rank_le_two (L : Subgroup G) [Group.IsPerfect L]
    (e : L ⧸ center L ≃* S) (hZ : Nat.Coprime p (Nat.card (center L)))
    (hL : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2) :
    primeRank p (action L e).range ≤ 2 := by
  let f := (action L e).rangeRestrict
  let : Finite (action L e).range := Finite.of_surjective f (action L e).rangeRestrict_surjective
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_coprime L e hZ hL hG
  exact (primeRank_le_of_surjective_of_coprime p f (action L e).rangeRestrict_surjective hk).trans
    ((primeRank_subgroup_le p (normalizer (L : Set G))).trans hG)

end Theory.GroupAction.ComponentRankAction
