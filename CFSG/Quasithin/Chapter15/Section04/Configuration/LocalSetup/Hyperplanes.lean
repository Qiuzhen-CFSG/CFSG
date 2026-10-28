module

public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.Defs
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankWitness

/-!
# The central-hyperplane calculation in Section 15.4

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma 15.4.14, printed p.1161.

A common nonidentity fixed point of `X` and `Y` is an involution. Its centralizer
is a two-local overgroup of both `XT` and `YT`, contradicting their distinct
unique maximal two-local overgroups. The intersection inequality for relative
indices then bounds `|Z|` by four when both fixed subgroups are hyperplanes.
The separate lower bound `|Z| > 2` forces equality, and the two ranks are computed
for the actual elementary abelian subgroup.

These are conditional steps: construction of the hyperplanes from 15.4.12(6)
and exclusion of rank at most one using 15.4.7 and 15.4.11(2) remain with the
source assembly. None of those missing facts is inferred from this file alone.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Different unique maximal two-local overgroups separate the fixed hyperplanes
inside an elementary abelian two-subgroup centralizing `T`. -/
theorem centralizers_disjoint_of_unique
    {T Z X Y M₁ M₂ : Subgroup G} [IsElementaryAbelian 2 Z]
    (hTC : T ≤ centralizer (Z : Set G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ T ≤ M → M = M₂)
    (hne : M₁ ≠ M₂) :
    (Z ⊓ centralizer (X : Set G)) ⊓ (Z ⊓ centralizer (Y : Set G)) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  change z = 1
  by_contra hzne
  have hzorder : orderOf z = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian z hz.1.1, hzne⟩
  obtain ⟨M, hCM, hM⟩ := Finite.exists_le_maximal
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hzorder)
  have hT : T ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hTC ht) z hz.1.1).symm)
  have hX : X ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.1.2 x hx)
  have hY : Y ≤ centralizer ({z} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.2.2 y hy)
  exact hne ((huniqueX M hM ((sup_le hX hT).trans hCM)).symm.trans
    (huniqueY M hM ((sup_le hY hT).trans hCM)))

/-- The index calculation in 15.4.14: disjoint hyperplanes bound the order by four.
The lower bound is to be discharged from 15.4.7 and 15.4.11(2). -/
theorem card_eq_four_of_unique_hyperplanes
    {T Z X Y M₁ M₂ : Subgroup G} [IsElementaryAbelian 2 Z]
    (hTC : T ≤ centralizer (Z : Set G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ T ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hX : (Z ⊓ centralizer (X : Set G)).relIndex Z = 2)
    (hY : (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2)
    (hlarge : 2 < Nat.card Z) : Nat.card Z = 4 := by
  have hdisjoint := centralizers_disjoint_of_unique hTC huniqueX huniqueY hne
  have hi : ((Z ⊓ centralizer (X : Set G)) ⊓
      (Z ⊓ centralizer (Y : Set G))).relIndex Z ≤
      (Z ⊓ centralizer (X : Set G)).relIndex Z *
      (Z ⊓ centralizer (Y : Set G)).relIndex Z := relIndex_inf_le
  rw [hdisjoint, relIndex_bot_left, hX, hY] at hi
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 Z).exists_card_eq
  have hnlt : 1 < n := by
    by_contra hnlt
    have hnle : n ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hnle
    omega
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hi
  have hne : n = 2 := by omega
  simpa [hne] using hn

/-- Order four is rank two for the actual elementary subgroup. -/
theorem rank_eq_two_of_card_four (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hcard : Nat.card Z = 4) : Group.rank Z = 2 ∧ primeRank 2 Z = 2 := by
  have hupper : Group.rank Z ≤ 2 := IsElementaryAbelian.rank_le_of_card_le (p := 2) Z (by omega)
  have hlower : 2 ≤ Group.rank Z := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
    have hpow : ∀ z : Z, z ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Z)
    simpa only [hcard] using card_dvd_exponent_pow_rank' Z hpow
  have hpupper : primeRank 2 Z ≤ 2 := IsElementaryAbelian.primeRank_le_of_card_le Z (by omega)
  have hplower : 2 ≤ primeRank 2 Z := by
    apply primeRank_ge_of_elementary_embedding (A := Z)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Z))
      (by simpa using hcard) (MonoidHom.id Z) Function.injective_id
  exact ⟨le_antisymm hupper hlower, le_antisymm hpupper hplower⟩

omit [Finite G] in
/-- A hyperplane in the rank-two center is a nontrivial subgroup of order two. -/
theorem centralizer_card_two_of_hyperplane {Z Y : Subgroup G}
    (hcard : Nat.card Z = 4)
    (hY : (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2) :
    Nat.card ↥(Z ⊓ centralizer (Y : Set G)) = 2 ∧ Z ⊓ centralizer (Y : Set G) ≠ ⊥ := by
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Z ⊓ centralizer (Y : Set G)) Z bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, hY, hcard] at hm
  have hc : Nat.card ↥(Z ⊓ centralizer (Y : Set G)) = 2 := by omega
  refine ⟨hc, ?_⟩
  intro hb
  rw [hb, card_bot] at hc
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
