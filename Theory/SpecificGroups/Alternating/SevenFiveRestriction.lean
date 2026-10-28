module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# Perfect intermediate subgroups above a Sylow-normalized A₅ in A₇

The A₅ fixes two letters. Together with its normalizing Sylow two-subgroup
it generates their setwise stabilizer, which is maximal in A₇. A perfect
intermediate subgroup normalized by the same Sylow subgroup therefore
is the A₅ or the whole A₇: inside the stabilizer perfectness removes its
index-two quotient, while in the other case Sylow normalization gives
normality in A₇. This retains the hypothesis that excludes A₅ < A₆ < A₇.

Source: Aschbacher–Smith A.3.14(2), printed pp.49–50, in the application
to 12.3.12, printed p.811. The original two-core quotient and central
cover are handled by SevenFiveRestrictionLift and the Chapter 12 adapter.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.SpecificGroups.Alternating.SevenFivePlacement
local notation "A7" => alternatingGroup (Fin 7)

private theorem pair_index_le_two (i j : Fin 7) (hij : i ≠ j) :
    ((fixingSubgroup A7 ({i,j} : Set (Fin 7))).subgroupOf
      (stabilizer A7 ({i,j} : Set (Fin 7)))).index ≤ 2 := by
  classical
  let s : Set (Fin 7) := {i,j}
  let N := stabilizer A7 s
  let f : N →* Equiv.Perm s := MulAction.toPermHom N s
  have hk : (fixingSubgroup A7 s).subgroupOf N = f.ker := by
    ext x
    change (∀ y : s, x.val • y.val = y.val) ↔ f x = 1
    constructor
    · intro h
      apply Equiv.ext
      intro y
      exact Subtype.ext (h y)
    · intro h y
      exact congrArg Subtype.val (Equiv.congr_fun h y)
  change ((fixingSubgroup A7 s).subgroupOf N).index ≤ 2
  rw [hk, index_ker]
  have hc : Nat.card (Equiv.Perm s) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hs : Fintype.card s = 2 := by simpa only [Set.fintypeCard_eq_ncard] using Set.ncard_pair hij
    rw [hs]
    rfl
  exact hc ▸ Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective

private theorem pair_stabilizer_contains_normalizer
    (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (i j : Fin 7) (hij : i ≠ j)
    (hB : B = fixingSubgroup A7 ({i,j} : Set (Fin 7))) :
    normalizer (B : Set A7) ≤ stabilizer A7 ({i,j} : Set (Fin 7)) := by
  classical
  have hpair : ({i,j} : Set (Fin 7)) ⊆ fixedPoints B (Fin 7) := by
    intro x hx b
    have hb : b.val ∈ fixingSubgroup A7 ({i,j} : Set (Fin 7)) := hB ▸ b.property
    exact hb ⟨x,hx⟩
  have hfixed : fixedPoints B (Fin 7) = {i,j} := by
    exact (Set.eq_of_subset_of_ncard_le hpair (by
      rw [fixed_card_two B e S hSN, Set.ncard_pair hij])).symm
  intro g hg
  apply (mem_stabilizer_set' (Set.toFinite _)).mpr
  intro x hx
  rw [← hfixed] at hx ⊢
  intro b
  have hb := (mem_normalizer_iff''.mp hg b.val).mp b.property
  have hh := hx ⟨g⁻¹ * b.val * g,hb⟩
  change (g⁻¹ * b.val * g) • x = x at hh
  have hh' := congrArg (fun y : Fin 7 => g • y) hh
  change b.val • (g • x) = g • x
  simpa only [smul_smul, mul_inv_cancel_left, mul_assoc] using hh'

/-- A full Sylow two-subgroup and its normalized A₅ generate the maximal
setwise stabilizer of the two fixed letters. -/
theorem sylow_sup_five_isCoatom (B : Subgroup A7)
    (e : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 A7)
    (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7)) :
    IsCoatom (B ⊔ (S : Subgroup A7)) := by
  classical
  obtain ⟨i,j,hij,hB⟩ := exists_fixed_pair B e S hSN
  let N := stabilizer A7 ({i,j} : Set (Fin 7))
  have hn : normalizer (B : Set A7) ≤ N :=
    pair_stabilizer_contains_normalizer B e S hSN i j hij hB
  have hBN : B ≤ N := B.le_normalizer.trans hn
  have hcB : Nat.card B = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi : (B.subgroupOf N).index ≤ 2 := hB ▸ pair_index_le_two i j hij
  have hcN : Nat.card N ≤ 120 := by
    have hc := (B.subgroupOf N).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv,hcB] at hc
    omega
  have hcS : Nat.card S = 8 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Sylow.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel
  have hcJ : 120 ≤ Nat.card (B ⊔ (S : Subgroup A7) : Subgroup A7) := by
    have h60 : 60 ∣ Nat.card (B ⊔ (S : Subgroup A7) : Subgroup A7) :=
      hcB ▸ card_dvd_of_le (le_sup_left : B ≤ B ⊔ (S : Subgroup A7))
    have h8 : 8 ∣ Nat.card (B ⊔ (S : Subgroup A7) : Subgroup A7) :=
      hcS ▸ card_dvd_of_le (le_sup_right : (S : Subgroup A7) ≤ B ⊔ (S : Subgroup A7))
    have hd : 120 ∣ Nat.card (B ⊔ (S : Subgroup A7) : Subgroup A7) :=
      (show Nat.lcm 60 8 = 120 by decide) ▸ Nat.lcm_dvd h60 h8
    exact Nat.le_of_dvd (Nat.card_pos) hd
  have he : B ⊔ (S : Subgroup A7) = N :=
    eq_of_le_of_card_ge (sup_le hBN (hSN.trans hn)) (hcN.trans hcJ)
  rw [he]
  apply alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl
  · exact ⟨i,by simp,j,by simp,hij⟩
  · have hc := Set.ncard_add_ncard_compl ({i,j} : Set (Fin 7))
    rw [Set.ncard_pair hij,Nat.card_fin] at hc
    rw [Set.ncard_pair hij]
    omega

/-- The A₇ restriction with both inherited Sylow normalizations. The
intermediate subgroup is perfect; subgroup inclusion alone is insufficient. -/
theorem perfect_overgroup_eq_or_top (B E : Subgroup A7)
    (e : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 A7)
    (hSB : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (hSE : (S : Subgroup A7) ≤ normalizer (E : Set A7))
    (hBE : B ≤ E) [Group.IsPerfect E] : E = B ∨ E = ⊤ := by
  classical
  have hm := sylow_sup_five_isCoatom B e S hSB
  have hle : B ⊔ (S : Subgroup A7) ≤ E ⊔ (S : Subgroup A7) := sup_le_sup_right hBE _
  rcases lt_or_eq_of_le hle with hlt | heq
  · have ht : E ⊔ (S : Subgroup A7) = ⊤ := hm.2 _ hlt
    let : E.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [← ht]
      exact sup_le E.le_normalizer hSE))
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 7))
        (N := E) with hbot | htop
    · have hBbot : B = ⊥ := bot_unique (hbot ▸ hBE)
      have hc : Nat.card B = 60 := by
        rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      rw [hBbot,card_bot] at hc
      omega
    · exact Or.inr htop
  · obtain ⟨i,j,hij,hB⟩ := exists_fixed_pair B e S hSB
    let N := stabilizer A7 ({i,j} : Set (Fin 7))
    have hn := pair_stabilizer_contains_normalizer B e S hSB i j hij hB
    have hBN : B ≤ N := B.le_normalizer.trans hn
    have hEN : E ≤ N := (le_sup_left : E ≤ E ⊔ (S : Subgroup A7)).trans
      (heq ▸ sup_le hBN (hSB.trans hn))
    let : Group.IsPerfect (E.subgroupOf N) := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hEN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hEN).symm.surjective
    have hEB := le_of_isPerfect_of_index_le_two (E.subgroupOf N) (B.subgroupOf N)
      (hB ▸ pair_index_le_two i j hij)
    have h := map_mono (f := N.subtype) hEB
    rw [map_subgroupOf_eq_of_le hEN,map_subgroupOf_eq_of_le hBN] at h
    exact Or.inl (le_antisymm h hBE)
end Theory.SpecificGroups.Alternating.SevenFivePlacement
