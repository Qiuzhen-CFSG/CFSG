module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.SixPoint
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.Alternating.theorem_5_2_1_2

/-!
# Six-point images of the four literal Held pairs

For the first pair in each local subgroup we use the native six-letter action.
For the second we compose it with the pentad automorphism of S₆. The restrictions
of the published candidate words are checked in these coordinates. Short words
in the six resulting generators give every transposition preserving a fixed
four-point set, so the actual pair product maps onto its full set stabilizer.

The stabilizer preimage equality additionally requires containment of the
native action kernel in the pair product. That concrete Held calculation is
left explicit; surjectivity of the six-point action alone does not imply it.

Sources: GLS3 Table 5.3p; the unchanged ATLAS max3/max4 programs and degree-2058
representation; the literal words in LocalActions.Candidates. GAP right-action
permutations are already inverted by the Held carrier, so word order is unchanged.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry


@[expose] def twist (j : Fin 2) : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) :=
  if j = 0 then MonoidHom.id _ else GLS3.Chapter5.outerHom

theorem twist_bijective (j : Fin 2) : Function.Bijective (twist j) := by
  fin_cases j
  · exact Function.bijective_id
  · exact GLS3.Chapter5.outerHom_bijective

@[expose] noncomputable def action (i : Bool) (j : Fin 2) :
    localOvergroup i →* Equiv.Perm (Fin 6) := (twist j).comp (SixPoint.action i)

@[expose] noncomputable def quotientAction (i : Bool) (j : Fin 2) :
    LocalQuotient i →* Equiv.Perm (Fin 6) := (twist j).comp (SixPoint.quotientAction i)

theorem quotientAction_mk (i : Bool) (j : Fin 2) (g : localOvergroup i) :
    quotientAction i j (localQuotientMap i g) = action i j g := rfl

theorem action_surjective (i : Bool) (j : Fin 2) : Function.Surjective (action i j) :=
  (twist_bijective j).surjective.comp (SixPoint.action_surjective i)

theorem quotientAction_surjective (i : Bool) (j : Fin 2) :
    Function.Surjective (quotientAction i j) :=
  (twist_bijective j).surjective.comp (SixPoint.quotientAction_surjective i)

theorem action_ker (i : Bool) (j : Fin 2) : (action i j).ker = (SixPoint.action i).ker := by
  ext g
  change twist j (SixPoint.action i g) = 1 ↔ SixPoint.action i g = 1
  simpa only [map_one] using (twist_bijective j).injective.eq_iff (a := SixPoint.action i g) (b := 1)

/-- Images of the first local generator in the two six-point actions. -/
@[expose] def first (i : Bool) (j : Fin 2) : Equiv.Perm (Fin 6) where
  toFun := match i, j with
    | false, 0 => ![0, 1, 5, 3, 4, 2]
    | false, 1 => ![4, 3, 5, 1, 0, 2]
    | true, 0 => ![5, 1, 2, 3, 4, 0]
    | true, 1 => ![3, 2, 1, 0, 5, 4]
  invFun := match i, j with
    | false, 0 => ![0, 1, 5, 3, 4, 2]
    | false, 1 => ![4, 3, 5, 1, 0, 2]
    | true, 0 => ![5, 1, 2, 3, 4, 0]
    | true, 1 => ![3, 2, 1, 0, 5, 4]
  left_inv := by cases i <;> fin_cases j <;> decide
  right_inv := by cases i <;> fin_cases j <;> decide

/-- Images of the second local generator in the two six-point actions. -/
@[expose] def second (i : Bool) (j : Fin 2) : Equiv.Perm (Fin 6) where
  toFun := match i, j with
    | false, 0 => ![2, 4, 5, 1, 0, 3]
    | false, 1 => ![1, 0, 3, 5, 4, 2]
    | true, 0 => ![0, 4, 5, 1, 2, 3]
    | true, 1 => ![4, 2, 5, 3, 1, 0]
  invFun := match i, j with
    | false, 0 => ![4, 3, 0, 5, 1, 2]
    | false, 1 => ![1, 0, 5, 2, 4, 3]
    | true, 0 => ![0, 3, 4, 5, 1, 2]
    | true, 1 => ![5, 4, 1, 3, 0, 2]
  left_inv := by cases i <;> fin_cases j <;> decide
  right_inv := by cases i <;> fin_cases j <;> decide

/-- Images of oddWord 0, oddWord 1, and the four twoWord generators, in order. -/
@[expose] def imageGenerator (i : Bool) (j : Fin 2) (k : Fin 6) : Equiv.Perm (Fin 6) where
  toFun := match i, j, k with
    | false, 0, 0 => ![0, 1, 2, 3, 4, 5]
    | false, 0, 1 => ![2, 1, 5, 3, 4, 0]
    | false, 0, 2 => ![5, 4, 2, 3, 1, 0]
    | false, 0, 3 => ![5, 1, 2, 3, 4, 0]
    | false, 0, 4 => ![2, 1, 0, 5, 4, 3]
    | false, 0, 5 => ![0, 1, 2, 3, 4, 5]
    | false, 1, 0 => ![0, 1, 2, 3, 4, 5]
    | false, 1, 1 => ![0, 1, 3, 5, 4, 2]
    | false, 1, 2 => ![0, 4, 2, 3, 1, 5]
    | false, 1, 3 => ![0, 4, 5, 3, 1, 2]
    | false, 1, 4 => ![5, 1, 3, 2, 4, 0]
    | false, 1, 5 => ![0, 1, 2, 3, 4, 5]
    | true, 0, 0 => ![0, 1, 4, 3, 5, 2]
    | true, 0, 1 => ![0, 1, 5, 3, 2, 4]
    | true, 0, 2 => ![0, 1, 4, 3, 2, 5]
    | true, 0, 3 => ![0, 3, 4, 1, 2, 5]
    | true, 0, 4 => ![4, 1, 5, 3, 0, 2]
    | true, 0, 5 => ![0, 1, 2, 3, 4, 5]
    | true, 1, 0 => ![0, 1, 2, 3, 4, 5]
    | true, 1, 1 => ![5, 1, 2, 0, 4, 3]
    | true, 1, 2 => ![0, 2, 1, 3, 4, 5]
    | true, 1, 3 => ![3, 2, 1, 0, 4, 5]
    | true, 1, 4 => ![5, 1, 2, 4, 3, 0]
    | true, 1, 5 => ![0, 1, 2, 3, 4, 5]
  invFun := match i, j, k with
    | false, 0, 0 => ![0, 1, 2, 3, 4, 5]
    | false, 0, 1 => ![5, 1, 0, 3, 4, 2]
    | false, 0, 2 => ![5, 4, 2, 3, 1, 0]
    | false, 0, 3 => ![5, 1, 2, 3, 4, 0]
    | false, 0, 4 => ![2, 1, 0, 5, 4, 3]
    | false, 0, 5 => ![0, 1, 2, 3, 4, 5]
    | false, 1, 0 => ![0, 1, 2, 3, 4, 5]
    | false, 1, 1 => ![0, 1, 5, 2, 4, 3]
    | false, 1, 2 => ![0, 4, 2, 3, 1, 5]
    | false, 1, 3 => ![0, 4, 5, 3, 1, 2]
    | false, 1, 4 => ![5, 1, 3, 2, 4, 0]
    | false, 1, 5 => ![0, 1, 2, 3, 4, 5]
    | true, 0, 0 => ![0, 1, 5, 3, 2, 4]
    | true, 0, 1 => ![0, 1, 4, 3, 5, 2]
    | true, 0, 2 => ![0, 1, 4, 3, 2, 5]
    | true, 0, 3 => ![0, 3, 4, 1, 2, 5]
    | true, 0, 4 => ![4, 1, 5, 3, 0, 2]
    | true, 0, 5 => ![0, 1, 2, 3, 4, 5]
    | true, 1, 0 => ![0, 1, 2, 3, 4, 5]
    | true, 1, 1 => ![3, 1, 2, 5, 4, 0]
    | true, 1, 2 => ![0, 2, 1, 3, 4, 5]
    | true, 1, 3 => ![3, 2, 1, 0, 4, 5]
    | true, 1, 4 => ![5, 1, 2, 4, 3, 0]
    | true, 1, 5 => ![0, 1, 2, 3, 4, 5]
  left_inv := by cases i <;> fin_cases j <;> fin_cases k <;> decide
  right_inv := by cases i <;> fin_cases j <;> fin_cases k <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem twist_first (i : Bool) (j : Fin 2) : twist j (SixPoint.first i) = first i j := by
  cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem twist_second (i : Bool) (j : Fin 2) : twist j (SixPoint.second i) = second i j := by
  cases i <;> fin_cases j <;> decide +kernel

@[expose] def wordElement (i : Bool) (w : List (Bool × ℤ)) : localOvergroup i :=
  ⟨LocalActions.evalLocalWord i w, LocalActions.evalLocalWord_mem i w⟩

@[expose] def wordImage (i : Bool) (j : Fin 2) (w : List (Bool × ℤ)) : Equiv.Perm (Fin 6) :=
  (w.map fun t => (if t.1 then second i j else first i j) ^ t.2).prod

theorem action_word (i : Bool) (j : Fin 2) (w : List (Bool × ℤ)) :
    action i j (wordElement i w) = wordImage i j w := by
  induction w with
  | nil => exact (action i j).map_one
  | cons t w ih =>
    rcases t with ⟨b, n⟩
    cases b
    · change action i j ((⟨Held.a, a_mem_localOvergroup i⟩ : localOvergroup i) ^ n * wordElement i w) =
        first i j ^ n * wordImage i j w
      rw [map_mul, map_zpow, ih]
      have h : action i j ⟨Held.a, a_mem_localOvergroup i⟩ = first i j := by
        change twist j (SixPoint.action i ⟨Held.a, _⟩) = first i j
        rw [SixPoint.action_first, twist_first]
      rw [h]
    · change action i j ((⟨localWord i, localWord_mem_localOvergroup i⟩ : localOvergroup i) ^ n * wordElement i w) =
        second i j ^ n * wordImage i j w
      rw [map_mul, map_zpow, ih]
      have h : action i j ⟨localWord i, localWord_mem_localOvergroup i⟩ = second i j := by
        change twist j (SixPoint.action i ⟨localWord i, _⟩) = second i j
        rw [SixPoint.action_second, twist_second]
      rw [h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem action_oddWord (i : Bool) (j : Fin 2) (k : Fin 2) :
    action i j (wordElement i (LocalActions.oddWord i j k)) = imageGenerator i j ⟨k.val, by omega⟩ := by
  rw [action_word]
  cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem action_twoWord (i : Bool) (j : Fin 2) (k : Fin 4) :
    action i j (wordElement i (LocalActions.twoWord i j k)) = imageGenerator i j ⟨k.val + 2, by omega⟩ := by
  rw [action_word]
  cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

@[reducible, expose] def block (i : Bool) (j : Fin 2) : Set (Fin 6) :=
  ↑(if i then (if j = 0 then {0, 2, 4, 5} else {0, 3, 4, 5}) else {0, 2, 3, 5} : Finset (Fin 6))

private instance blockDecidable (i : Bool) (j : Fin 2) (x : Fin 6) : Decidable (x ∈ block i j) := by
  unfold block
  infer_instance

theorem block_ncard (i : Bool) (j : Fin 2) : (block i j).ncard = 4 := by
  cases i <;> fin_cases j <;> simp [block]

theorem zero_mem_block (i : Bool) (j : Fin 2) : (0 : Fin 6) ∈ block i j := by
  cases i <;> fin_cases j <;> simp [block]

@[expose] def pairProduct (i : Bool) (j : Fin 2) : Subgroup Held.He :=
  LocalActions.candidateOdd i j ⊔ LocalActions.candidateTwo i j

theorem pairProduct_le_localOvergroup (i : Bool) (j : Fin 2) :
    pairProduct i j ≤ localOvergroup i :=
  sup_le (LocalActions.candidateOdd_le_localOvergroup i j) (LocalActions.candidateTwo_le_localOvergroup i j)


/-- Images can be computed before or after taking the intrinsic two-core quotient. -/
theorem map_localImage (i : Bool) (j : Fin 2) (H : Subgroup Held.He) :
    (localImage i H).map (quotientAction i j) =
      (H.subgroupOf (localOvergroup i)).map (action i j) := by
  change ((H.subgroupOf (localOvergroup i)).map (localQuotientMap i)).map _ = _
  rw [map_map]
  rfl

private theorem subgroupOf_closure_range {G A : Type*} [Group G] (M : Subgroup G)
    (g : A → G) (hg : ∀ a, g a ∈ M) :
    (closure (Set.range g)).subgroupOf M = closure (Set.range (fun a => (⟨g a, hg a⟩ : M))) := by
  apply map_injective M.subtype_injective
  rw [map_subgroupOf_eq_of_le ((closure_le _).mpr (by rintro _ ⟨a, rfl⟩; exact hg a)),
    MonoidHom.map_closure, ← Set.range_comp]
  rfl

private theorem imageGenerator_preserves (i : Bool) (j : Fin 2) (k : Fin 6) :
    imageGenerator i j k ∈ MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j) := by
  rw [MulAction.mem_stabilizer_set]
  change ∀ x, imageGenerator i j k x ∈ block i j ↔ x ∈ block i j
  cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem pairProduct_image_le_stabilizer (i : Bool) (j : Fin 2) :
    ((pairProduct i j).subgroupOf (localOvergroup i)).map (action i j) ≤
      MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j) := by
  rw [pairProduct, subgroupOf_sup (LocalActions.candidateOdd_le_localOvergroup i j)
    (LocalActions.candidateTwo_le_localOvergroup i j), Subgroup.map_sup]
  apply sup_le
  · rw [LocalActions.candidateOdd, subgroupOf_closure_range _ _ (fun _ => LocalActions.evalLocalWord_mem i _),
      MonoidHom.map_closure, ← Set.range_comp]
    apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change action i j (wordElement i _) ∈ _
    rw [action_oddWord]
    exact imageGenerator_preserves i j _
  · rw [LocalActions.candidateTwo, subgroupOf_closure_range _ _ (fun _ => LocalActions.evalLocalWord_mem i _),
      MonoidHom.map_closure, ← Set.range_comp]
    apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change action i j (wordElement i _) ∈ _
    rw [action_twoWord]
    exact imageGenerator_preserves i j _

theorem imageGenerator_mem_pairProduct_image (i : Bool) (j : Fin 2) (k : Fin 6) :
    imageGenerator i j k ∈ ((pairProduct i j).subgroupOf (localOvergroup i)).map (action i j) := by
  have ho (t : Fin 2) : imageGenerator i j ⟨t.val, by omega⟩ ∈
      ((pairProduct i j).subgroupOf (localOvergroup i)).map (action i j) :=
    ⟨wordElement i (LocalActions.oddWord i j t),
      (show LocalActions.candidateOdd i j ≤ pairProduct i j from le_sup_left)
        (subset_closure (Set.mem_range_self t)), action_oddWord i j t⟩
  have ht (t : Fin 4) : imageGenerator i j ⟨t.val + 2, by omega⟩ ∈
      ((pairProduct i j).subgroupOf (localOvergroup i)).map (action i j) :=
    ⟨wordElement i (LocalActions.twoWord i j t),
      (show LocalActions.candidateTwo i j ≤ pairProduct i j from le_sup_right)
        (subset_closure (Set.mem_range_self t)), action_twoWord i j t⟩
  fin_cases k
  · exact ho 0
  · exact ho 1
  · exact ht 0
  · exact ht 1
  · exact ht 2
  · exact ht 3

private theorem ofSubtype_mem_of_swaps {A : Type*} [Finite A] [DecidableEq A]
    (p : A → Prop) [DecidablePred p] (H : Subgroup (Equiv.Perm A))
    (hs : ∀ x y, p x → p y → Equiv.swap x y ∈ H) (g : Equiv.Perm {x // p x}) :
    Equiv.Perm.ofSubtype g ∈ H := by
  induction g using Equiv.Perm.swap_induction_on with
  | one => simpa only [map_one] using H.one_mem
  | swap_mul g x y _ ih =>
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
    exact H.mul_mem (hs x y x.property y.property) ih

private theorem stabilizer_le_of_swaps {A : Type*} [Finite A] [DecidableEq A]
    (B : Set A) (H : Subgroup (Equiv.Perm A))
    (hs : ∀ x y, (x ∈ B ↔ y ∈ B) → Equiv.swap x y ∈ H) :
    MulAction.stabilizer (Equiv.Perm A) B ≤ H := by
  classical
  intro g hg
  have hp : ∀ x, g x ∈ B ↔ x ∈ B := MulAction.mem_stabilizer_set.mp hg
  let u := g.subtypePerm hp
  let v := g.subtypePerm (p := (· ∉ B)) (fun x => not_congr (hp x))
  have hu : Equiv.Perm.ofSubtype u ∈ H :=
    ofSubtype_mem_of_swaps (· ∈ B) H (fun x y hx hy => hs x y (iff_of_true hx hy)) u
  have hv : Equiv.Perm.ofSubtype v ∈ H :=
    ofSubtype_mem_of_swaps (· ∉ B) H (fun x y hx hy => hs x y (iff_of_false hx hy)) v
  have he : g = Equiv.Perm.ofSubtype u * Equiv.Perm.ofSubtype v := by
    ext x
    by_cases hx : x ∈ B
    · simp [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_not_mem,
        Equiv.Perm.ofSubtype_apply_of_mem, hx, u, v]
    · simp [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_not_mem,
        Equiv.Perm.ofSubtype_apply_of_mem, hx, (hp x).not.mpr hx, u, v]
  rw [he]
  exact H.mul_mem hu hv

private def swapWordAsc : Bool → Fin 2 → Fin 6 → Fin 6 → List (Fin 6)
  | false, 0, 0, 2 => [3, 1]
  | false, 0, 0, 3 => [1, 4, 3]
  | false, 0, 0, 5 => [3]
  | false, 0, 1, 4 => [2, 3]
  | false, 0, 2, 3 => [4, 3, 4]
  | false, 0, 2, 5 => [1, 3]
  | false, 0, 3, 5 => [3, 1, 4]
  | false, 1, 0, 2 => [1, 2, 4, 3]
  | false, 1, 0, 3 => [2, 4, 3, 4]
  | false, 1, 0, 5 => [2, 3, 1, 4]
  | false, 1, 1, 4 => [2]
  | false, 1, 2, 3 => [2, 3, 1]
  | false, 1, 2, 5 => [2, 3]
  | false, 1, 3, 5 => [1, 2, 3]
  | true, 0, 0, 2 => [1, 4, 2]
  | true, 0, 0, 4 => [0, 2, 4]
  | true, 0, 0, 5 => [4, 2, 4]
  | true, 0, 1, 3 => [2, 3]
  | true, 0, 2, 4 => [2]
  | true, 0, 2, 5 => [0, 2]
  | true, 0, 4, 5 => [1, 2]
  | true, 1, 0, 3 => [2, 3]
  | true, 1, 0, 4 => [1, 2, 4, 3]
  | true, 1, 0, 5 => [2, 3, 1]
  | true, 1, 1, 2 => [2]
  | true, 1, 3, 4 => [2, 3, 1, 4]
  | true, 1, 3, 5 => [1, 2, 3]
  | true, 1, 4, 5 => [2, 4, 3, 4]
  | _, _, _, _ => []

private def swapWord (i : Bool) (j : Fin 2) (x y : Fin 6) : List (Fin 6) :=
  if x ≤ y then swapWordAsc i j x y else swapWordAsc i j y x

private theorem swapWord_spec (i : Bool) (j : Fin 2) :
    ∀ x y : Fin 6, (x ∈ block i j ↔ y ∈ block i j) →
      ((swapWord i j x y).map (imageGenerator i j)).prod = Equiv.swap x y := by
  cases i <;> fin_cases j <;> decide +kernel

/-- The actual candidate product maps onto the entire set stabilizer. -/
theorem pairProduct_image_eq_stabilizer (i : Bool) (j : Fin 2) :
    ((pairProduct i j).subgroupOf (localOvergroup i)).map (action i j) =
      MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j) := by
  apply le_antisymm (pairProduct_image_le_stabilizer i j)
  apply stabilizer_le_of_swaps
  intro x y hxy
  rw [← swapWord_spec i j x y hxy]
  apply Subgroup.list_prod_mem
  intro p hp
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact imageGenerator_mem_pairProduct_image i j k

/-- The small permutation calculation leaves precisely the kernel containment
needed to identify the stabilizer preimage in M/O₂(M). -/
theorem stabilizer_preimage_of_kernel (i : Bool) (j : Fin 2)
    (hker : (SixPoint.action i).ker ≤ (pairProduct i j).subgroupOf (localOvergroup i)) :
    (MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j)).comap (quotientAction i j) =
      localImage i (pairProduct i j) := by
  have hkq : (localQuotientMap i).ker ≤ (pairProduct i j).subgroupOf (localOvergroup i) := by
    simpa only [localQuotientMap, QuotientGroup.ker_mk'] using
      (SixPoint.twoCore_le_ker_action i).trans hker
  apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 (localOvergroup i)))
  change ((MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j)).comap
      (quotientAction i j)).comap (localQuotientMap i) =
    ((pairProduct i j).subgroupOf (localOvergroup i) |>.map (localQuotientMap i)).comap
      (localQuotientMap i)
  rw [comap_map_eq_self hkq]
  change (MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j)).comap (action i j) = _
  rw [← pairProduct_image_eq_stabilizer]
  exact comap_map_eq_self (by rwa [action_ker])

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
