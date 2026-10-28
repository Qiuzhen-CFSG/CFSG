module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCartan
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.PrimeOrderConjugation
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The elementary order-twenty-seven contradiction in 5.2.2

The genuine left Hall Cartan is cyclic, so its B-invariant subgroup of
prime order is normalized by B. When B is an elementary group of order
nine and D has order three, this action is trivial. If B normalizes L₂
and D moves L₂, the two subgroups are disjoint. Their literal join is
therefore elementary abelian of order 27 inside M=N_G(L), contradicting
the odd-prime rank bound for this two-local subgroup.

The final application retains the cubic-plane conclusion and movement
of L₂ explicitly. Those are outputs of the changed-Sylow and component
arguments on p.648, not consequences asserted by this module.

Source: Aschbacher--Smith, 5.2.2, final paragraph, printed p.649
(`refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Cyclicity of the actual left Hall Cartan makes each prime actor B-invariant. -/
theorem CartanPair.normalizes_prime_actor {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D) : B ≤ normalizer (D : Set G) := by
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  exact c.right_normalizes_left.trans
    (normalizer_le_normalizer_of_le_cyclic D A hd.le_cartan)

/-- A three-group acts trivially on the actual cubic subgroup. -/
theorem CartanPair.centralizes_cubic_actor {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H 3 D) (hBp : IsPGroup 3 B) :
    B ≤ centralizer (D : Set G) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Normalizes B D := ⟨c.normalizes_prime_actor h hd⟩
  have ht := actsTrivially_of_isPGroup_on_cyclic_prime_order
    (A := B) (G := D) (by decide) hBp (isCyclic_of_prime_card hd.card) hd.card
  intro b hb d hD
  have he := congrArg Subtype.val (ht (⟨b, hb⟩ : B) (⟨d, hD⟩ : D))
  change b * d * b⁻¹ = d at he
  have hh := congrArg (fun x : G => x * b) he
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm

/-- The independent cubic and the original elementary plane generate E₂₇. -/
theorem CartanPair.cubic_plane_join {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H 3 D) (hBe : IsElementaryAbelian 3 B)
    (hBcard : Nat.card B = 9) (hDB : ¬ D ≤ B) :
    IsElementaryAbelian 3 (D ⊔ B : Subgroup G) ∧
      Nat.card (D ⊔ B : Subgroup G) = 27 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hd.card
  let : IsElementaryAbelian 3 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun d => by
      simpa only [hd.card] using (pow_card_eq_one' (x := d))) }
  let := hBe
  have hc := c.centralizes_cubic_actor h hd (IsElementaryAbelian.isPGroup 3 B)
  have hdis : Disjoint D B := by
    let : Fact (Nat.card D).Prime := ⟨hd.card ▸ (by decide : Nat.Prime 3)⟩
    rcases (B.subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply disjoint_iff.mpr
      apply eq_bot_iff.mpr
      intro x hx
      have hx' : (⟨x, hx.1⟩ : D) ∈ B.subgroupOf D := hx.2
      rw [hb] at hx'
      exact congrArg Subtype.val (mem_bot.mp hx')
    · exact (hDB (subgroupOf_eq_top.mp ht)).elim
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hc, ?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D B
    (hc.trans (Subgroup.centralizer_le_normalizer _)) hdis, hd.card, hBcard]

/-- Apply the elementary obstruction in the literal maximal two-local N_G(L). -/
theorem Input.prime_actor_excluded_of_cubic_plane {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H 3 D) (hBe : IsElementaryAbelian 3 B)
    (hBcard : Nat.card B = 9) (hB : B ≤ normalizer (L₂ : Set G))
    (hD : ¬ D ≤ normalizer (L₂ : Set G)) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨he, hcard⟩ := c.cubic_plane_join h hd hBe hBcard (fun hh => hD (hh.trans hB))
  let := he
  let M := normalizer (L : Set G)
  have hJM : D ⊔ B ≤ M := sup_le
    ((hd.le_cartan.trans c.left_le).trans (inf_le_left.trans L.le_normalizer))
    (c.right_le.trans inf_le_left)
  let : IsElementaryAbelian 3 ((D ⊔ B).subgroupOf M) :=
    IsElementaryAbelian.subgroupOf hJM
  have hsize : Nat.card ((D ⊔ B).subgroupOf M) = 3 ^ 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv, hcard]
    norm_num
  have hlower := IsElementaryAbelian.primeRank_ge_of_card ((D ⊔ B).subgroupOf M) hsize
  have hupper := isQuasithin_iff_twoLocal.mp h.qtke.quasithin M h.maximal.1
    3 (by decide) (by decide)
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
