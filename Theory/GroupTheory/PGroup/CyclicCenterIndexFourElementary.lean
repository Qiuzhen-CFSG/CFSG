module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.IndexTwoIntersection
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary subgroups above a cyclic center of index four

An elementary subgroup joined with the center is abelian, hence proper in
 a nonabelian group. Its image modulo the center therefore has order at
most two, as does its intersection with the cyclic center. This bounds its
order by four. In an index-two extension, every elementary eight must cross
the core, and its normalizer has twice the order of its core intersection.

These intrinsic reductions support the cyclic-tail calculation in
Janko–Thompson (1970), §4, Case 2, printed p.393.
-/

open Subgroup
open scoped IsMulCommutative

/-- A nonabelian group whose cyclic center has index four has no elementary
binary subgroup larger than four. No ambient rank assumption is used. -/
public theorem Subgroup.card_elementary_le_four_of_cyclic_center_index_four {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hn : ¬ IsMulCommutative P) (hi : (center P).index = 4)
    (E : Subgroup P) [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  let Z := center P
  have hab : IsMulCommutative (E ⊔ Z : Subgroup P) := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr
        (sup_le E.le_centralizer (show Z ≤ centralizer (E : Set P) from center_le_centralizer _))
    · exact center_le_centralizer _
  have hproper : E ⊔ Z ≠ ⊤ := by
    intro heq
    have ht : IsMulCommutative (⊤ : Subgroup P) := heq ▸ hab
    exact hn (isMulCommutative_iff.mpr (fun x y =>
      congrArg Subtype.val (ht.is_comm.comm ⟨x, mem_top x⟩ ⟨y, mem_top y⟩)))
  have hidx : 2 ≤ (E ⊔ Z).index := by
    have hpos := (E ⊔ Z).index_ne_zero_of_finite
    have hne : (E ⊔ Z).index ≠ 1 := fun h => hproper (index_eq_one.mp h)
    omega
  have hrel := relIndex_mul_index (show Z ≤ E ⊔ Z from le_sup_right)
  rw [relIndex_sup_right, hi] at hrel
  have hbound : Z.relIndex E ≤ 2 := by nlinarith
  let I := Z.subgroupOf E
  let f : I →* Z := {
    toFun x := ⟨x.1.1, x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : IsCyclic I := isCyclic_of_injective f (fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Z => (z : P)) h)))
  have hIc : Nat.card I ≤ 2 := by
    have he : Monoid.exponent I ∣ 2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x))
    rw [IsCyclic.exponent_eq_card] at he
    exact Nat.le_of_dvd (by decide) he
  have hcount := I.card_mul_index
  change Nat.card I * Z.relIndex E = Nat.card E at hcount
  nlinarith

/-- An elementary eight crosses any subgroup satisfying the preceding rank bound. -/
public theorem Subgroup.elementary_eight_not_le_of_cyclic_center_index_four
    {P : Type*} [Group P] [Finite P] (R : Subgroup P)
    [IsCyclic (center R)] (hn : ¬ IsMulCommutative R)
    (hi : (center R).index = 4)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8) :
    ¬ F ≤ R := by
  intro hle
  let : IsElementaryAbelian 2 (F.subgroupOf R) := IsElementaryAbelian.subgroupOf hle
  have hbound := card_elementary_le_four_of_cyclic_center_index_four hn hi (F.subgroupOf R)
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hF] at hbound
  omega

/-- Crossing an index-two subgroup halves the order of an elementary eight. -/
public theorem Subgroup.card_intersection_four_of_elementary_eight_not_le
    {P : Type*} [Group P] [Finite P] (R F : Subgroup P)
    (hi : R.index = 2) (hF : Nat.card F = 8) (hout : ¬ F ≤ R) :
    Nat.card (R.subgroupOf F) = 4 := by
  have h := (R.subgroupOf F).card_mul_index
  rw [R.subgroupOf_index_eq_two F hi hout, hF] at h
  omega

/-- The normalizer of a subgroup crossing an index-two subgroup also crosses it. -/
public theorem Subgroup.card_normalizer_eq_two_mul_core_intersection
    {P : Type*} [Group P] [Finite P] (R F : Subgroup P)
    (hi : R.index = 2) (hout : ¬ F ≤ R) :
    Nat.card (normalizer (F : Set P)) =
      2 * Nat.card (R.subgroupOf (normalizer (F : Set P))) := by
  have hN : ¬ normalizer (F : Set P) ≤ R := fun h => hout (F.le_normalizer.trans h)
  have h := (R.subgroupOf (normalizer (F : Set P))).card_mul_index
  rw [R.subgroupOf_index_eq_two _ hi hN] at h
  omega
