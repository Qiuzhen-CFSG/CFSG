module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

/-!
# Counting a partition by conjugate subgroups

A partition of the nonidentity elements gives the sum of `|U| - 1` over
its members. Grouping the members into conjugacy classes and applying
orbit--stabilizer gives the normalized sum `( |U| - 1 ) / |N(U)|`.
This is the elementary partition count used, for example, in
Huppert--Blackburn, *Finite Groups III*, XI.3.10(i).
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Count the nonidentity elements in a finite subgroup partition. -/
public theorem sum_card_sub_one_of_partition (P : Finset (Subgroup G))
    (hP : ∀ x : G, x ≠ 1 → ∃! U : Subgroup G, U ∈ P ∧ x ∈ U) :
    (∑ U ∈ P, (Nat.card U - 1)) = Nat.card G - 1 := by
  classical
  let := Fintype.ofFinite G
  have hcard (U : Subgroup G) :
      Nat.card U - 1 = ∑ x ∈ Finset.univ.erase (1 : G), if x ∈ U then 1 else 0 := by
    rw [← Finset.sum_filter]
    have heq : ((Finset.univ.erase (1 : G)).filter (fun x => x ∈ U)) =
        (Finset.univ.filter (fun x => x ∈ U)).erase 1 := by ext; simp [and_comm]
    rw [heq, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem (by simp)]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  have hone (x : G) (hx : x ∈ Finset.univ.erase (1 : G)) :
      (∑ U ∈ P, if x ∈ U then 1 else 0) = (1 : ℕ) := by
    obtain ⟨U, ⟨hUP, hxU⟩, huniq⟩ := hP x (Finset.mem_erase.mp hx).1
    rw [Finset.sum_eq_single U]
    · simp [hxU]
    · intro V hVP hne
      have hxV : x ∉ V := fun hxV => hne (huniq V ⟨hVP, hxV⟩)
      simp [hxV]
    · exact fun h => (h hUP).elim
  rw [Finset.sum_congr rfl hone]
  simp [Nat.card_eq_fintype_card]

omit [Finite G] in
/-- The relative index times the subgroup order is the overgroup order. -/
public theorem relIndex_mul_card_of_le {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have hc := (H.subgroupOf K).index_mul_card
  rwa [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv] at hc

open scoped Pointwise

private noncomputable instance conjugationAction : MulAction G (Subgroup G) :=
  MulAction.compHom (Subgroup G) ConjAct.toConjAct.toMonoidHom

private noncomputable def conjugates (U : Subgroup G) : Finset (Subgroup G) :=
  (MulAction.orbit G U).toFinite.toFinset

private theorem mem_conjugates (U V : Subgroup G) :
    V ∈ conjugates U ↔ ∃ g : G, V = U.map (MulAut.conj g).toMonoidHom := by
  classical
  simp only [conjugates, Set.Finite.mem_toFinset, MulAction.mem_orbit_iff]
  exact exists_congr (fun g => eq_comm)

private theorem card_conjugates (U : Subgroup G) :
    (conjugates U).card = (normalizer (U : Set G)).index := by
  have hs : MulAction.stabilizer G U = normalizer (U : Set G) := by
    ext g
    exact conjAct_pointwise_smul_iff
  classical
  let := Fintype.ofFinite (MulAction.orbit G U)
  rw [conjugates, Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G U), hs]
  rfl

/-- Count a partition specified by one representative of each subgroup
conjugacy class. No orders or number of classes are prescribed. -/
public theorem sum_normalizer_index_mul_card_sub_one_of_partition
    (S : Finset (Subgroup G))
    (hS : ∀ U ∈ S, ∀ V ∈ S, (∃ g : G, V = U.map (MulAut.conj g).toMonoidHom) → U = V)
    (hP : ∀ x : G, x ≠ 1 → ∃! V : Subgroup G,
      (∃ U ∈ S, ∃ g : G, V = U.map (MulAut.conj g).toMonoidHom) ∧ x ∈ V) :
    (∑ U ∈ S, (normalizer (U : Set G)).index * (Nat.card U - 1)) =
      Nat.card G - 1 := by
  classical
  have hdis : (S : Set (Subgroup G)).PairwiseDisjoint conjugates := by
    intro U hU V hV hne
    apply Finset.disjoint_left.mpr
    intro W hWU hWV
    have hWU' : W ∈ MulAction.orbit G U := by simpa only [conjugates, Set.Finite.mem_toFinset] using hWU
    have hWV' : W ∈ MulAction.orbit G V := by simpa only [conjugates, Set.Finite.mem_toFinset] using hWV
    have hUV : V ∈ MulAction.orbit G U :=
      (MulAction.orbit_eq_iff.mpr hWV').symm.trans
        (MulAction.orbit_eq_iff.mpr hWU') |>.le (MulAction.mem_orbit_self V)
    exact hne (hS U hU V hV ((mem_conjugates U V).mp
      (by simpa only [conjugates, Set.Finite.mem_toFinset] using hUV)))
  have hcount := sum_card_sub_one_of_partition (S.biUnion conjugates) (fun x hx => by
    simpa only [Finset.mem_biUnion, mem_conjugates] using hP x hx)
  rw [Finset.sum_biUnion hdis] at hcount
  convert hcount using 1
  apply Finset.sum_congr rfl
  intro U _
  have hc : ∀ V ∈ conjugates U, Nat.card V = Nat.card U := by
    intro V hV
    obtain ⟨g, rfl⟩ := (mem_conjugates U V).mp hV
    exact card_map_of_injective (MulAut.conj g).injective
  simp_rw [Finset.sum_congr rfl (fun V hV => congrArg (fun n : ℕ => n - 1) (hc V hV))]
  simp [card_conjugates]

/-- Divide the conjugate-subgroup partition count by the ambient group order. -/
public theorem sum_card_sub_one_div_normalizer_card_of_partition
    (S : Finset (Subgroup G))
    (hS : ∀ U ∈ S, ∀ V ∈ S, (∃ g : G, V = U.map (MulAut.conj g).toMonoidHom) → U = V)
    (hP : ∀ x : G, x ≠ 1 → ∃! V : Subgroup G,
      (∃ U ∈ S, ∃ g : G, V = U.map (MulAut.conj g).toMonoidHom) ∧ x ∈ V) :
    (∑ U ∈ S, ((Nat.card U : ℚ) - 1) / Nat.card (normalizer (U : Set G))) =
      1 - 1 / (Nat.card G : ℚ) := by
  have hcount := sum_normalizer_index_mul_card_sub_one_of_partition S hS hP
  have hcast : (∑ U ∈ S, ((normalizer (U : Set G)).index : ℚ) *
      ((Nat.card U : ℚ) - 1)) = (Nat.card G : ℚ) - 1 := by
    have hsub (U : Subgroup G) : ((Nat.card U - 1 : ℕ) : ℚ) = (Nat.card U : ℚ) - 1 :=
      by rw [Nat.cast_sub (Nat.card_pos (α := U)), Nat.cast_one]
    simpa only [Nat.cast_sum, Nat.cast_mul, hsub,
      Nat.cast_sub (Nat.card_pos (α := G)), Nat.cast_one] using congrArg (Nat.cast : ℕ → ℚ) hcount
  have hG : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  apply (mul_left_inj' hG).mp
  rw [Finset.sum_mul]
  calc
    _ = ∑ U ∈ S, ((normalizer (U : Set G)).index : ℚ) * ((Nat.card U : ℚ) - 1) := by
      apply Finset.sum_congr rfl
      intro U _
      have hN : (Nat.card (normalizer (U : Set G)) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := normalizer (U : Set G))).ne'
      have h := (normalizer (U : Set G)).index_mul_card
      have hh : ((normalizer (U : Set G)).index : ℚ) * Nat.card (normalizer (U : Set G)) =
          (Nat.card G : ℚ) := by exact_mod_cast h
      rw [← hh]
      field_simp
    _ = _ := by rw [hcast]; field_simp

end Subgroup
