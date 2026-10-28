module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Data
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.ElementaryAbelian.Basic

/-!
# Soundness of the finite Held extension checks

In an elementary abelian two-group, adjoining one element adds at most its
single coset. This makes conjugate membership a finite test using the proposed
node member lists. A normal elementary extension passes the square, commutation
and conjugation tests; the remaining acceptance check proves both subgroup
inclusions against the proposed target. All equalities are in the actual Held
carrier, detected on its certified four-point base.

The membership lists and the Boolean branch tests are explicit, unproved inputs
to the final implication. This module certifies the checker, not the 23,552
individual computations. It uses no normal-form surjectivity, ambient order,
simplicity, or prior subgroup enumeration.

Source: the literal subgroup words and extension discovery retained in
`IntrinsicEnumeration/source/`, for GLS3 Table 5.3p and the Held local calculation.
-/

@[expose] public section

open scoped IsMulCommutative

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
open LocalPairs.SylowGeometry.Calculations

private theorem mem_join_iff {G : Type*} [Group G] (H : Subgroup G) (g : G)
    [IsElementaryAbelian 2 ↥(H ⊔ Subgroup.zpowers g)] (x : G) :
    x ∈ H ⊔ Subgroup.zpowers g ↔ x ∈ H ∨ g * x ∈ H := by
  let E := H ⊔ Subgroup.zpowers g
  have hg : g ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hH : H ≤ E := le_sup_left
  have hs (y : G) (hy : y ∈ E) : y * y = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy
  have hc (y : G) (hy : y ∈ E) : g * y = y * g := setLike_mul_comm hg hy
  have hmem (y : G) (hy : y ∈ H ∨ g * y ∈ H) : y ∈ E := by
    rcases hy with hy | hy
    · exact hH hy
    · have hm := E.mul_mem hg (hH hy)
      simpa only [← mul_assoc, hs g hg, one_mul] using hm
  let K : Subgroup G :=
    { carrier := {y | y ∈ H ∨ g * y ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        intro a b ha hb
        have haE := hmem a ha
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (H.mul_mem ha hb)
        · right
          have hm := H.mul_mem ha hb
          rw [← mul_assoc, ← hc a haE, mul_assoc] at hm
          exact hm
        · right
          simpa only [mul_assoc] using H.mul_mem ha hb
        · left
          have hm := H.mul_mem ha hb
          have he : (g * a) * (g * b) = a * b := by
            rw [hc a haE, mul_assoc, ← mul_assoc g g b, hs g hg, one_mul]
          rwa [he] at hm
      inv_mem' := by
        intro a ha
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hs a (hmem a ha))
        rwa [hai] }
  constructor
  · intro hx
    have hle : E ≤ K := sup_le (fun y hy => Or.inl hy)
      (Subgroup.zpowers_le.mpr (Or.inr (by simpa only [hs g hg] using H.one_mem)))
    exact hle hx
  · exact hmem x

/-- Equality is tested on the certified four-point base of the actual Held action. -/
def same (x y : representative) : Bool :=
  decide (∀ k : Fin 4, representation x.val ⟨k.val, by omega⟩ =
    representation y.val ⟨k.val, by omega⟩)

theorem same_eq_true {x y : representative} : same x y = true ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (Held.eq_of_four_point_images (of_decide_eq_true h))
  · rintro rfl
    exact decide_eq_true (fun _ => rfl)

/-- Test for membership in the proposed finite list of a node. -/
def memberCheck (i : Option (Fin 22)) (x : representative) : Bool :=
  (members i).any (fun m => same x (normalForm m))

/-- Test the two cosets of a node obtained by adjoining an involution. -/
def cosetCheck (i : Option (Fin 22)) (n : Fin 1024) (x : representative) : Bool :=
  memberCheck i x || memberCheck i (normalForm n * x)

/-- The new element must square to one. -/
def squareCheck (n : Fin 1024) : Bool := same (normalForm n * normalForm n) 1

/-- The new element must commute with the original generators of the node. -/
def commuteCheck (i : Option (Fin 22)) (n : Fin 1024) : Bool :=
  (rowGenerators i).all (fun w => same (normalForm n * word w) (word w * normalForm n))

/-- The original four generators must conjugate the new element into the two cosets. -/
def conjugateCheck (i : Option (Fin 22)) (n : Fin 1024) : Bool :=
  (List.finRange 4).all (fun k =>
    let g : representative := ⟨generator k, generator_mem k⟩
    cosetCheck i n (g⁻¹ * normalForm n * g))

/-- Both inclusions required for the proposed extension equality. -/
def acceptedCheck (i : Option (Fin 22)) (n : Fin 1024) (j : Option (Fin 22)) : Bool :=
  memberCheck j (normalForm n) &&
    (rowGenerators i).all (fun w => memberCheck j (word w)) &&
    (rowGenerators j).all (fun w => cosetCheck i n (word w))

/-- Reject by a necessary condition, or verify both inclusions for the target. -/
def branchCheck (i : Option (Fin 22)) (n : Fin 1024) : Bool :=
  !squareCheck n || !commuteCheck i n || !conjugateCheck i n ||
    acceptedCheck i n (target i n)

theorem memberCheck_eq_true
    (hmem : ∀ (i : Option (Fin 22)) (x : representative),
      x ∈ node i ↔ ∃ m ∈ members i, normalForm m = x)
    (i : Option (Fin 22)) (x : representative) :
    memberCheck i x = true ↔ x ∈ node i := by
  rw [hmem i x]
  simp only [memberCheck, List.any_eq_true, same_eq_true]
  constructor <;> rintro ⟨m, hm, h⟩ <;> exact ⟨m, hm, h.symm⟩

theorem cosetCheck_eq_true
    (hmem : ∀ (i : Option (Fin 22)) (x : representative),
      x ∈ node i ↔ ∃ m ∈ members i, normalForm m = x)
    (i : Option (Fin 22)) (n : Fin 1024)
    [IsElementaryAbelian 2 (extension i n)] (x : representative) :
    cosetCheck i n x = true ↔ x ∈ extension i n := by
  let : IsElementaryAbelian 2 ↥(node i ⊔ Subgroup.zpowers (normalForm n)) :=
    (inferInstance : IsElementaryAbelian 2 (extension i n))
  rw [cosetCheck, Bool.or_eq_true, memberCheck_eq_true hmem, memberCheck_eq_true hmem]
  exact (mem_join_iff (node i) (normalForm n) x).symm

private theorem word_mem_node (i : Option (Fin 22)) (w : List ℤ)
    (hw : w ∈ rowGenerators i) : word w ∈ node i := by
  cases i with
  | none => simp [rowGenerators] at hw
  | some j => exact word_mem_entry j w hw

private theorem node_le_of_generators (i : Option (Fin 22))
    (K : Subgroup representative)
    (h : ∀ w ∈ rowGenerators i, word w ∈ K) : node i ≤ K := by
  cases i with
  | none => exact bot_le
  | some j =>
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨w, hw, rfl⟩
    exact h w hw

/-- Checked rejection or checked inclusions imply the required literal equality.
The finite node membership premise and the Boolean check are kept explicit. -/
theorem eq_target_of_branchCheck
    (hmem : ∀ (i : Option (Fin 22)) (x : representative),
      x ∈ node i ↔ ∃ m ∈ members i, normalForm m = x)
    (i : Option (Fin 22)) (n : Fin 1024) (hcheck : branchCheck i n = true)
    (hnormal : (extension i n).Normal)
    (helem : IsElementaryAbelian 2 (extension i n)) :
    extension i n = node (target i n) := by
  let := helem
  have hs : squareCheck n = true := by
    apply same_eq_true.mpr
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (normalForm n) (normalForm_mem_extension i n)
  have hc : commuteCheck i n = true := by
    apply List.all_eq_true.mpr
    intro w hw
    apply same_eq_true.mpr
    exact setLike_mul_comm (normalForm_mem_extension i n)
      (node_le_extension i n (word_mem_node i w hw))
  have hn : conjugateCheck i n = true := by
    apply List.all_eq_true.mpr
    intro k _
    apply (cosetCheck_eq_true hmem i n _).mpr
    exact hnormal.conj_mem' _ (normalForm_mem_extension i n) _
  have ha : acceptedCheck i n (target i n) = true := by
    simpa only [branchCheck, hs, hc, hn, Bool.not_true, Bool.false_or] using hcheck
  simp only [acceptedCheck, Bool.and_eq_true] at ha
  obtain ⟨⟨hx, hi⟩, hj⟩ := ha
  apply le_antisymm
  · apply sup_le
    · apply node_le_of_generators
      intro w hw
      exact (memberCheck_eq_true hmem _ _).mp (List.all_eq_true.mp hi w hw)
    · exact Subgroup.zpowers_le.mpr ((memberCheck_eq_true hmem _ _).mp hx)
  · apply node_le_of_generators
    intro w hw
    exact (cosetCheck_eq_true hmem i n _).mp (List.all_eq_true.mp hj w hw)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
