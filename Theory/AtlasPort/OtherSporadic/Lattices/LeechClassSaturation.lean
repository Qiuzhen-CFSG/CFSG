/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechClassSaturation.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechClassCapacity

/-!
Every mod-two class is represented in the zero or three small shells.
The shell counts and capacity bounds saturate the finite quotient, fixing every nonempty fiber size.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable
instance (r : ℤ) : Fintype (LeechShell r) := Fintype.ofFinite _
instance : Fintype LeechModTwo := Fintype.ofFinite _

def shellClasses (r : ℤ) : Finset LeechModTwo :=
  Finset.univ.image (fun x : LeechShell r => leechReduction x.val)

theorem shellFiber_card (r : ℤ) (a : LeechModTwo) :
    Nat.card (ShellClassFiber r a) = (Finset.univ.filter (fun x : LeechShell r => leechReduction x.val = a)).card := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

theorem shellClasses_capacity (r : ℤ) (n : ℕ)
    (hb : ∀ a, Nat.card (ShellClassFiber r a) ≤ n) : Nat.card (LeechShell r) ≤ n * (shellClasses r).card := by
  have h := Finset.card_le_mul_card_image (f := fun x : LeechShell r => leechReduction x.val)
    Finset.univ n (fun a _ => by rw [← shellFiber_card]; exact hb a)
  simpa only [shellClasses,Finset.card_univ,← Nat.card_eq_fintype_card] using h

theorem shellClasses_zero_not_mem (r : ℤ) (hr : 0 < r ∧ r ≤ 8) : 0 ∉ shellClasses r := by
  intro h
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
  exact leech_short_shell_class_nonzero r hr x hx

theorem shellClasses_disjoint (r s : ℤ) (hr : r ≤ 8) (hs : s ≤ 8) (hne : r ≠ s) :
    Disjoint (shellClasses r) (shellClasses s) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp ha
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hb
  have hn1 := leech_shell_halfNorm r x
  have hn2 := leech_shell_halfNorm s y
  exact leech_different_short_classes x.val y.val (by omega) (by omega) (hx.trans hy.symm)

def shortClasses : Finset LeechModTwo := {0} ∪ (shellClasses 4 ∪ (shellClasses 6 ∪ shellClasses 8))

theorem shortClasses_card : shortClasses.card =
    1 + (shellClasses 4).card + (shellClasses 6).card + (shellClasses 8).card := by
  have h46 := shellClasses_disjoint 4 6 (by decide) (by decide) (by decide)
  have h48 := shellClasses_disjoint 4 8 (by decide) (by decide) (by decide)
  have h68 := shellClasses_disjoint 6 8 (by decide) (by decide) (by decide)
  have h0 : Disjoint ({0} : Finset LeechModTwo) (shellClasses 4 ∪ (shellClasses 6 ∪ shellClasses 8)) := by
    apply Finset.disjoint_singleton_left.mpr
    simp only [Finset.mem_union,not_or]
    exact ⟨shellClasses_zero_not_mem 4 (by decide),shellClasses_zero_not_mem 6 (by decide),
      shellClasses_zero_not_mem 8 (by decide)⟩
  rw [shortClasses,Finset.card_union_of_disjoint h0,
    Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨h46,h48⟩),
    Finset.card_union_of_disjoint h68,Finset.card_singleton]
  omega

theorem shellClasses_counts : (shellClasses 4).card = 98280 ∧
    (shellClasses 6).card = 8386560 ∧ (shellClasses 8).card = 8292375 := by
  have h4 := shellClasses_capacity 4 2 (short_class_capacity 4 (by decide))
  have h6 := shellClasses_capacity 6 2 (short_class_capacity 6 (by decide))
  have h8 := shellClasses_capacity 8 48 norm_eight_class_capacity
  rw [leech_minimal_shell_card] at h4
  rw [leech_six_shell_card] at h6
  rw [leech_eight_shell_card] at h8
  have ht := Finset.card_le_univ shortClasses
  rw [shortClasses_card,← Nat.card_eq_fintype_card,leechModTwo_card] at ht
  norm_num at ht
  omega

theorem shortClasses_eq_univ : shortClasses = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [shortClasses_card,shellClasses_counts.1,shellClasses_counts.2.1,shellClasses_counts.2.2,
    ← Nat.card_eq_fintype_card,leechModTwo_card]
  norm_num

theorem shellFiber_saturation (r : ℤ) (n : ℕ)
    (hb : ∀ a, Nat.card (ShellClassFiber r a) ≤ n)
    (ht : Nat.card (LeechShell r) = n * (shellClasses r).card) (a : LeechModTwo)
    (ha : a ∈ shellClasses r) : Nat.card (ShellClassFiber r a) = n := by
  have hs : (∑ b ∈ shellClasses r, Nat.card (ShellClassFiber r b)) =
      ∑ _b ∈ shellClasses r, n := by
    change (∑ b ∈ Finset.univ.image (fun x : LeechShell r => leechReduction x.val), Nat.card (ShellClassFiber r b)) = _
    simp_rw [shellFiber_card]
    rw [← Finset.card_eq_sum_card_image]
    simp only [Finset.card_univ,Finset.sum_const,nsmul_eq_mul,← Nat.card_eq_fintype_card]
    simpa only [mul_comm,Nat.cast_id] using ht
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hb b)).mp hs a ha

theorem norm_eight_fiber_card (a : LeechModTwo) (ha : a ∈ shellClasses 8) :
    Nat.card (ShellClassFiber 8 a) = 48 := by
  apply shellFiber_saturation 8 48 norm_eight_class_capacity ?_ a ha
  rw [leech_eight_shell_card,shellClasses_counts.2.2]

theorem norm_four_fiber_card (a : LeechModTwo) (ha : a ∈ shellClasses 4) :
    Nat.card (ShellClassFiber 4 a) = 2 := by
  apply shellFiber_saturation 4 2 (short_class_capacity 4 (by decide)) ?_ a ha
  rw [leech_minimal_shell_card,shellClasses_counts.1]

theorem norm_six_fiber_card (a : LeechModTwo) (ha : a ∈ shellClasses 6) :
    Nat.card (ShellClassFiber 6 a) = 2 := by
  apply shellFiber_saturation 6 2 (short_class_capacity 6 (by decide)) ?_ a ha
  rw [leech_six_shell_card,shellClasses_counts.2.1]

end Atlas.Lattices
