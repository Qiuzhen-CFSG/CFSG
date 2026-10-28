module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Rectangles
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue.Certificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Elementary subgroups of order 64 in the marked Sylow model

Write the ten upper entries of UT₅(2) as coordinates. If a commuting family
of square-one matrices contains an element with nonzero (0,1) entry, five
commutation equations determine three other entries of every member. The
small binary certificate bounds the family by 56. Reversing the basis gives
the same result at (3,4). An elementary subgroup of order 64 therefore has
both entries zero. The square equations then put each element in the 2+3
or 3+2 rectangle; a subgroup contained in the union lies in one rectangle.

This proves the order-64 catalogue used in Aschbacher, *Sporadic Groups*
(1994), 39.1(3), p.213. Its transport to the actual Sylow in G and the
application to fusion are in `SourceNormalizer.Catalogue`.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear Theory.SpecificGroups.LinearSylowNormalizers
private abbrev B := ZMod 2
private abbrev Mat := Matrix (Fin 5) (Fin 5) B
private def entries (v : Fin 10 → B) : Mat := !![
  1, v 0, v 1, v 2, v 3;
  0, 1, v 4, v 5, v 6;
  0, 0, 1, v 7, v 8;
  0, 0, 0, 1, v 9;
  0, 0, 0, 0, 1]
private def coordinates (m : Mat) : Fin 10 → B :=
  ![m 0 1, m 0 2, m 0 3, m 0 4, m 1 2, m 1 3, m 1 4, m 2 3, m 2 4, m 3 4]

private theorem entries_coordinates (g : SL) (hg : g ∈ upper) :
    entries (coordinates g.val) = g.val := by
  obtain ⟨hu, hd⟩ := (mem_unipotent 5 B g).mp (model_upper_eq_unipotent ▸ hg)
  have hu := (mem_borel 5 B g).mp hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entries, coordinates, hd]
  all_goals exact (hu (by decide)).symm

private theorem square_equations (v : Fin 10 → B) (h : entries v * entries v = 1) :
    v 0 * v 4 = 0 ∧ v 4 * v 7 = 0 ∧ v 7 * v 9 = 0 ∧
    v 0 * v 5 + v 1 * v 7 = 0 ∧ v 4 * v 8 + v 5 * v 9 = 0 ∧
    v 0 * v 6 + v 1 * v 8 + v 2 * v 9 = 0 := by
  have he (i j : Fin 5) := congrFun (congrFun h i) j
  have h02 := he 0 2
  have h13 := he 1 3
  have h24 := he 2 4
  have h03 := he 0 3
  have h14 := he 1 4
  have h04 := he 0 4
  simp [entries, Matrix.mul_apply, Fin.sum_univ_succ] at h02 h13 h24 h03 h14 h04
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert h02 using 1
    ring_nf
    simp only [show (2 : B) = 0 from rfl, mul_zero, add_zero]
  · convert h13 using 1
    ring_nf
    simp only [show (2 : B) = 0 from rfl, mul_zero, add_zero]
  · convert h24 using 1
    ring_nf
    simp only [show (2 : B) = 0 from rfl, mul_zero, add_zero]
  · convert h03 using 1
    ring_nf
    simp only [show (2 : B) = 0 from rfl, mul_zero, add_zero]
  · convert h14 using 1
    ring_nf
    simp only [show (2 : B) = 0 from rfl, mul_zero, add_zero]
  · convert h04 using 1
    ring_nf
    simp only [show (2 : B) = 0 from rfl, mul_zero, add_zero]

private theorem commute_equations (v w : Fin 10 → B)
    (h : entries v * entries w = entries w * entries v) :
    v 0 * w 4 = w 0 * v 4 ∧
    v 0 * w 5 + v 1 * w 7 = w 0 * v 5 + w 1 * v 7 ∧
    v 0 * w 6 + v 1 * w 8 + v 2 * w 9 = w 0 * v 6 + w 1 * v 8 + w 2 * v 9 ∧
    v 7 * w 9 = w 7 * v 9 ∧
    v 4 * w 8 + v 5 * w 9 = w 4 * v 8 + w 5 * v 9 := by
  have he (i j : Fin 5) := congrFun (congrFun h i) j
  have h02 := he 0 2
  have h03 := he 0 3
  have h04 := he 0 4
  have h24 := he 2 4
  have h14 := he 1 4
  simp [entries, Matrix.mul_apply, Fin.sum_univ_succ] at h02 h03 h04 h24 h14
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h02
  · linear_combination h03
  · linear_combination h04
  · linear_combination h24
  · linear_combination h14

private abbrev squareFamily := Catalogue.squareFamily

private theorem first_entry_card_le {α : Type*} [Finite α]
    (v : α → Fin 10 → B) (hv : Function.Injective v)
    (hs : ∀ a, entries (v a) * entries (v a) = 1)
    (hc : ∀ a b, entries (v a) * entries (v b) = entries (v b) * entries (v a))
    (a : α) (ha : v a 0 = 1) : Nat.card α ≤ 56 := by
  let x : Fin 5 → B := ![v a 1, v a 2, v a 7, v a 8, v a 9]
  have hsx := square_equations (v a) (hs a)
  have he : v a 4 = 0 := by simpa [ha] using hsx.1
  have hf : v a 5 = v a 1 * v a 7 := by
    have hh := hsx.2.2.2.1
    rw [ha, one_mul] at hh
    exact CharTwo.add_eq_zero.mp hh
  have hg : v a 6 = v a 1 * v a 8 + v a 2 * v a 9 := by
    have hh := hsx.2.2.2.2.2
    rw [ha, one_mul, add_assoc] at hh
    exact CharTwo.add_eq_zero.mp hh
  let short (b : α) : Fin 6 → B := ![v b 0, v b 1, v b 2, v b 7, v b 8, v b 9]
  have relations (b : α) :
      v b 4 = 0 ∧
      v b 5 = v b 0 * (x 0 * x 2) + x 0 * v b 7 + v b 1 * x 2 ∧
      v b 6 = v b 0 * (x 0 * x 3 + x 1 * x 4) +
        x 0 * v b 8 + v b 1 * x 3 + x 1 * v b 9 + v b 2 * x 4 := by
    obtain ⟨h02, h03, h04, _, _⟩ := commute_equations (v a) (v b) (hc a b)
    have he' : v b 4 = 0 := by simpa [ha, he] using h02
    refine ⟨he', ?_, ?_⟩
    · dsimp [x]
      rw [ha, one_mul, hf] at h03
      linear_combination (norm := (ring_nf; all_goals simp [show (2 : B) = 0 from rfl])) h03
    · dsimp [x]
      rw [ha, one_mul, hg] at h04
      linear_combination (norm := (ring_nf; all_goals simp [show (2 : B) = 0 from rfl])) h04
  have hm (b : α) : squareFamily x (short b) := by
    obtain ⟨he', hf', hg'⟩ := relations b
    dsimp [x] at hf' hg'
    obtain ⟨_, _, h24, h03, h14, h04⟩ := square_equations (v b) (hs b)
    obtain ⟨_, _, _, hc24, hc14⟩ := commute_equations (v a) (v b) (hc a b)
    simp only [he, he', zero_mul, zero_add, hf] at hc14 h14
    dsimp [squareFamily, Catalogue.squareFamily, short, x]
    refine ⟨h24, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hf'] using h03
    · simpa only [hf'] using h14
    · simpa only [hg'] using h04
    · exact CharTwo.add_eq_zero.mpr hc24
    · have hh := CharTwo.add_eq_zero.mpr hc14
      simpa only [hf'] using hh
  let f : α → { y : Fin 6 → B // squareFamily x y } × B :=
    fun b => (⟨short b, hm b⟩, v b 3)
  have hinj : Function.Injective f := by
    intro b c hh
    have hshort : short b = short c := congrArg (fun q => q.1.val) hh
    have h3 : v b 3 = v c 3 := congrArg Prod.snd hh
    have hsame (i : Fin 6) := congrFun hshort i
    have h0 := hsame 0
    have h1 := hsame 1
    have h2 := hsame 2
    have h7 := hsame 3
    have h8 := hsame 4
    have h9 := hsame 5
    dsimp [short] at h0 h1 h2 h7 h8 h9
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact (relations b).1.trans (relations c).1.symm
    · change v b 5 = v c 5
      rw [(relations b).2.1, (relations c).2.1, h0, h1, h7]
    · change v b 6 = v c 6
      rw [(relations b).2.2, (relations c).2.2, h0, h1, h2, h8, h9]
    · exact h7
    · exact h8
    · exact h9
  have hbound : Fintype.card {y : Fin 6 → B // squareFamily x y} ≤ 28 :=
    Catalogue.squareFamily_card x (show x 2 * x 4 = 0 from hsx.2.2.1)
  have hn := Nat.card_le_card_of_injective f hinj
  have hcard : Nat.card {y : Fin 6 → B // squareFamily x y} =
      Fintype.card {y : Fin 6 → B // squareFamily x y} := Nat.card_eq_fintype_card
  have hB : Nat.card B = 2 := by simp [B]
  rw [Nat.card_prod, hcard, hB] at hn
  exact hn.trans (Nat.mul_le_mul_right 2 hbound)


private def flip (m : Mat) : Mat := Matrix.reindex Fin.revPerm Fin.revPerm m.transpose
private theorem flip_mul (m n : Mat) : flip (m * n) = flip n * flip m := by
  unfold flip
  rw [Matrix.transpose_mul]
  exact (Matrix.reindexRingEquiv B Fin.revPerm).map_mul _ _
private theorem flip_one : flip 1 = 1 := by
  change (Matrix.reindexRingEquiv B Fin.revPerm) (1 : Mat).transpose = 1
  rw [Matrix.transpose_one, map_one]
private theorem flip_flip (m : Mat) : flip (flip m) = m := by
  ext i j
  exact congrArg₂ m (Fin.rev_rev i) (Fin.rev_rev j)
private def reverseCoordinates (v : Fin 10 → B) : Fin 10 → B :=
  ![v 9, v 8, v 6, v 3, v 7, v 5, v 2, v 4, v 1, v 0]
private theorem entries_reverse (v : Fin 10 → B) :
    entries (reverseCoordinates v) = flip (entries v) := by
  ext i j
  change entries (reverseCoordinates v) i j = entries v j.rev i.rev
  fin_cases i <;> fin_cases j <;> simp [entries, reverseCoordinates, Fin.rev]
private theorem coordinates_entries (v : Fin 10 → B) : coordinates (entries v) = v := by
  funext i
  fin_cases i <;> rfl
private theorem reverse_injective : Function.Injective reverseCoordinates := by
  intro v w h
  have hh := congrArg (fun t => flip (entries t)) h
  rw [entries_reverse, entries_reverse, flip_flip, flip_flip] at hh
  have := congrArg coordinates hh
  simpa only [coordinates_entries] using this

private theorem large_family_edge_zero {α : Type*} [Finite α]
    (v : α → Fin 10 → B) (hv : Function.Injective v)
    (hs : ∀ a, entries (v a) * entries (v a) = 1)
    (hc : ∀ a b, entries (v a) * entries (v b) = entries (v b) * entries (v a))
    (hcard : Nat.card α = 64) (a : α) : v a 0 = 0 ∧ v a 9 = 0 := by
  have hz (w : α → Fin 10 → B) (hw : Function.Injective w)
      (hws : ∀ b, entries (w b) * entries (w b) = 1)
      (hwc : ∀ b c, entries (w b) * entries (w c) = entries (w c) * entries (w b))
      (hn : Nat.card α = 64) (b : α) : w b 0 = 0 := by
    rcases (by decide : ∀ t : B, t = 0 ∨ t = 1) (w b 0) with h | h
    · exact h
    · have hh := first_entry_card_le w hw hws hwc b h
      omega
  refine ⟨hz v hv hs hc hcard a, ?_⟩
  apply hz (fun b => reverseCoordinates (v b)) (reverse_injective.comp hv) _ _ hcard a
  · intro b
    rw [entries_reverse, ← flip_mul, hs, flip_one]
  · intro b c
    rw [entries_reverse, entries_reverse, ← flip_mul, ← flip_mul, hc]


private theorem mem_plane_of_entries (g : SL) (v : Fin 10 → B)
    (hg : g.val = entries v) (h0 : v 0 = 0) (h7 : v 7 = 0)
    (h8 : v 8 = 0) (h9 : v 9 = 0) : g ∈ Model.plane := by
  let a := modelPlaneCoordinates.symm (Multiplicative.ofAdd
    (![![v 1, v 2, v 3], ![v 4, v 5, v 6]] : Fin 2 → Fin 3 → B))
  have he : (a : SL) = g := by
    apply Subtype.ext
    rw [modelPlaneCoordinates_matrix, hg]
    simp only [a, modelPlaneCoordinates.apply_symm_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entries, Matrix.single, h0, h7, h8, h9]
  exact he ▸ a.property

private abbrev tr {i j : Fin 5} (h : i < j) (a : B) : SL :=
  Matrix.SpecialLinearGroup.transvection (ne_of_lt h) a
private def threeWord (v : Fin 10 → B) : SL :=
  tr (by decide : (0 : Fin 5) < 3) (v 2) *
  tr (by decide : (0 : Fin 5) < 4) (v 3) *
  tr (by decide : (1 : Fin 5) < 3) (v 5) *
  tr (by decide : (1 : Fin 5) < 4) (v 6) *
  tr (by decide : (2 : Fin 5) < 3) (v 7) *
  tr (by decide : (2 : Fin 5) < 4) (v 8)
private theorem threeWord_val (v : Fin 10 → B) :
    (threeWord v).val = 1 + Matrix.single 0 3 (v 2) + Matrix.single 0 4 (v 3) +
      Matrix.single 1 3 (v 5) + Matrix.single 1 4 (v 6) +
      Matrix.single 2 3 (v 7) + Matrix.single 2 4 (v 8) := by
  simp [threeWord, tr, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]
private theorem threeWord_mem (v : Fin 10 → B) : threeWord v ∈ Model.threeSpace := by
  have h (i j : Fin 5) (hij : i < j) (hi : i.val < 3) (hj : 3 ≤ j.val) (a : B) :
      tr hij a ∈ Model.threeSpace := by
    rcases (by decide : ∀ a : B, a = 0 ∨ a = 1) a with rfl | rfl
    · simp
    · exact subset_closure ⟨i, j, hij, hi, hj, rfl⟩
  unfold threeWord
  repeat' apply Model.threeSpace.mul_mem
  all_goals exact h _ _ _ (by decide) (by decide) _
private theorem mem_threeSpace_of_entries (g : SL) (v : Fin 10 → B)
    (hg : g.val = entries v) (h0 : v 0 = 0) (h1 : v 1 = 0)
    (h4 : v 4 = 0) (h9 : v 9 = 0) : g ∈ Model.threeSpace := by
  have he : threeWord v = g := by
    apply Subtype.ext
    rw [hg, threeWord_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entries, Matrix.single, h0, h1, h4, h9]
  exact he ▸ threeWord_mem v

/-- Every order-64 elementary subgroup of the positive-root group lies in one
of the two literal rectangles. This is the catalogue part of source 39.1(3). -/
theorem model_elementary64_le_rectangle (A : Subgroup SL) (hA : A ≤ upper)
    (hEA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 64) :
    A ≤ Model.plane ∨ A ≤ Model.threeSpace := by
  let := hEA
  let v (a : A) := coordinates (a : SL).val
  have he (a : A) : entries (v a) = (a : SL).val := entries_coordinates a (hA a.property)
  have hv : Function.Injective v := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    rw [← he a, ← he b, hab]
  have hs (a : A) : entries (v a) * entries (v a) = 1 := by
    rw [he]
    exact congrArg (fun g : SL => g.val)
      (show (a : SL) * a = 1 by simpa only [pow_two] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : SL) a.property)
  have hc (a b : A) : entries (v a) * entries (v b) = entries (v b) * entries (v a) := by
    rw [he, he]
    exact congrArg (fun g : SL => g.val) (setLike_mul_comm a.property b.property)
  apply SubgroupClass.subset_union.mp
  intro g hg
  let a : A := ⟨g, hg⟩
  obtain ⟨h0, h9⟩ := large_family_edge_zero v hv hs hc hcard a
  obtain ⟨_, h47, _, h17, h48, h18⟩ := square_equations (v a) (hs a)
  simp only [h0, h9, zero_mul, mul_zero, zero_add, add_zero] at h17 h48 h18
  by_cases h1 : v a 1 = 0
  · by_cases h4 : v a 4 = 0
    · exact Or.inr (mem_threeSpace_of_entries g (v a) (he a).symm h0 h1 h4 h9)
    · exact Or.inl (mem_plane_of_entries g (v a) (he a).symm h0
        ((mul_eq_zero.mp h47).resolve_left h4) ((mul_eq_zero.mp h48).resolve_left h4) h9)
  · exact Or.inl (mem_plane_of_entries g (v a) (he a).symm h0
      ((mul_eq_zero.mp h17).resolve_left h1) ((mul_eq_zero.mp h18).resolve_left h1) h9)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
