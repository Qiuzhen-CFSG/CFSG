module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.Reduction
public import Theory.SpecificGroups.OddThreeRank
public import Theory.GroupTheory.SylowNormalCenterIntersection
public import Theory.ElementaryAbelian.Join

/-!
# Inner four-groups in the odd PSL₃ graph extension

The marked inner subgroup is the actual PSL₃ model, so its elementary
two-subgroups have order at most four. Consequently a large inner actor has
order exactly four. The normal inner subgroup meets the center of every
ambient Sylow subgroup in an involution. Adjoining that involution to any
large inner actor cannot increase its order; hence every such actor contains it.

These statements concern the original members of the family. No intersection
or subgroup of a member is inserted into the family. The centralizer residual
supplement below is the local subgroup used for E.1.2(E2); its component
conditions still require a separate matrix calculation.

Source: Aschbacher--Smith, E.1.2, E.1.5 and E.1.14(7), printed pp.210, 214;
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- Transport the proved two-rank bound through the marked inner equivalence. -/
theorem innerPart_primeRank_two_le {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) : primeRank 2 (innerPart F) ≤ 2 := by
  rw [← primeRank_equiv 2 (innerPartEquiv F)]
  exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF

/-- Every nontrivial large inner actor is a four-group. -/
theorem inner_actor_card_eq_four {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) {A : Subgroup (graphExtension F)}
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _)) (hne : A ≠ ⊥)
    (hAI : A ≤ innerPart F) : Nat.card A = 4 := by
  let := hΩ.1 A hA
  let : IsElementaryAbelian 2 (A.subgroupOf (innerPart F)) :=
    IsElementaryAbelian.subgroupOf hAI
  have hc : Nat.card A ≤ 2 ^ 2 := by
    have hh := (primeRank_le_iff_elementary_card_le (innerPart F)).mp
      (innerPart_primeRank_two_le F hp ho hF) (A.subgroupOf (innerPart F)) inferInstance
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv] at hh
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hc)
  have hn2 : n = 2 := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hcard1 : Nat.card A ≤ 2 ^ 1 := by
      rw [hn]
      exact pow_le_pow_right' (by decide) hn1
    have hr := IsElementaryAbelian.rank_le_of_card_le A hcard1
    have := hlarge A hA hAT hne
    omega
  simpa [hn2] using hn

/-- An inner Sylow-central involution belongs to every large inner actor. -/
theorem inner_actor_contains_central_involution {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) {A : Subgroup (graphExtension F)}
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _)) (hne : A ≠ ⊥)
    (hAI : A ≤ innerPart F) {z : graphExtension F} (hzI : z ∈ innerPart F)
    (hz2 : z ^ 2 = 1) (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    z ∈ A := by
  let := hΩ.1 A hA
  let : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hzC : z ∈ centralizer (A : Set _) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hTz (hAT ha))
  let : IsElementaryAbelian 2 (A ⊔ zpowers z : Subgroup _) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hzC)
  have hjoin : A ⊔ zpowers z ≤ innerPart F := sup_le hAI (zpowers_le.mpr hzI)
  let : IsElementaryAbelian 2 ((A ⊔ zpowers z).subgroupOf (innerPart F)) :=
    IsElementaryAbelian.subgroupOf hjoin
  have hc : Nat.card (A ⊔ zpowers z : Subgroup _) ≤ 4 := by
    have hh := (primeRank_le_iff_elementary_card_le (innerPart F)).mp
      (innerPart_primeRank_two_le F hp ho hF)
      ((A ⊔ zpowers z).subgroupOf (innerPart F)) inferInstance
    rwa [Nat.card_congr (subgroupOfEquivOfLe hjoin).toEquiv] at hh
  have he : A = A ⊔ zpowers z := eq_of_le_of_card_ge le_sup_left
    ((inner_actor_card_eq_four F hp ho hF hΩ hlarge hA hAT hne hAI).symm ▸ hc)
  have hzjoin : z ∈ A ⊔ zpowers z :=
    (show zpowers z ≤ A ⊔ zpowers z from le_sup_right) (mem_zpowers z)
  rwa [← he] at hzjoin

/-- Construct the common central involution without selecting a smaller actor. -/
theorem exists_common_inner_involution {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) (hi : HasInnerActor F T Ω) :
    ∃ z : graphExtension F, orderOf z = 2 ∧ z ∈ innerPart F ∧
      z ∈ (T : Subgroup _) ∧ (T : Subgroup _) ≤ centralizer ({z} : Set _) ∧
      ∀ A ∈ Ω, A ≤ (T : Subgroup _) → A ≠ ⊥ → A ≤ innerPart F → z ∈ A := by
  obtain ⟨A, hA, hAT, hne, hAI⟩ := hi
  have hfour := inner_actor_card_eq_four F hp ho hF hΩ hlarge hA hAT hne hAI
  have hd : 2 ∣ Nat.card (innerPart F) := by
    have h := card_dvd_of_le hAI
    rw [hfour] at h
    exact dvd_trans (by decide : 2 ∣ 4) h
  obtain ⟨x, hx, hx1, hxI⟩ := T.exists_ne_one_mem_center_of_normal (innerPart F) hd
  let n := orderOf x / 2
  have hxn : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (T.isPGroup'.dvd_orderOf hx1)
  let z : graphExtension F := (x ^ n : T)
  have hz : orderOf z = 2 := by simpa only [z, orderOf_coe] using hxn
  have hzI : z ∈ innerPart F := (innerPart F).pow_mem hxI n
  have hzT : z ∈ (T : Subgroup _) := (x ^ n : T).property
  have hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp ((center T).pow_mem hx n) ⟨t, ht⟩)
  refine ⟨z, hz, hzI, hzT, hTz, ?_⟩
  intro B hB hBT hne hBI
  exact inner_actor_contains_central_involution F hp ho hF hΩ hlarge hB hBT hne hBI
    hzI (hz ▸ pow_orderOf_eq_one z) hTz

/-- The intrinsic solvable residual of the full involution centralizer,
supplemented by the original ambient Sylow subgroup. -/
@[expose] def innerCentralizerSupplement (T : Sylow 2 (graphExtension F))
    (z : graphExtension F) : Subgroup (graphExtension F) :=
  (solvableResidual (centralizer ({z} : Set _))).map
    (centralizer ({z} : Set _)).subtype ⊔ (T : Subgroup _)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
