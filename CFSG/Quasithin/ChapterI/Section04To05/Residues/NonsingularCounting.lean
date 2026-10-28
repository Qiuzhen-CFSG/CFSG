module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NonsingularThird
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SingularTriples
public import Mathlib.Data.Set.Card

/-!
# Counting the nonsingular one-or-all triples

Three pairwise noncollinear points in a double-perp set have the same
15 common neighbors. Their closed neighborhoods each have 31 points.
Inclusion-exclusion therefore gives 63 points in the union, all the
original points. A point in two neighborhoods is in all three; every other
point is in exactly one. This is I.5.14 with the actual point counts.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup Theory.LinearAlgebra
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem closed_neighbors_card (x : S.Point) :
    Nat.card {y : S.Point // S.Collinear x y} = 31 := by
  let A := {y : S.Point // x ≠ y ∧ S.Collinear x y}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.c3_neighbors_card x]; decide)
  rw [Nat.card_congr (S.collinearOptionNeighborEquiv x), Finite.card_option, S.c3_neighbors_card x]

theorem commonNeighbors_eq_of_doublePerp (d : S.LocalPolarFacts) {x y z : S.Point}
    (hxy : ¬ S.Collinear x y) (hxz : ¬ S.Collinear x z) (hz : z ∈ S.DoublePerp x y) :
    {u : S.Point | S.Collinear x u ∧ S.Collinear y u} =
      {u : S.Point | S.Collinear x u ∧ S.Collinear z u} := by
  let : Finite S.Point := Nat.finite_of_card_ne_zero (by rw [S.c3_points_card d]; decide)
  apply Set.eq_of_subset_of_ncard_le
  · intro u hu
    exact ⟨hu.1, hz u hu.1 hu.2⟩
  · change Nat.card (S.CommonNeighbors x z) ≤ Nat.card (S.CommonNeighbors x y)
    rw [S.commonNeighbors_card d hxz, S.commonNeighbors_card d hxy]
  · exact Set.toFinite _

theorem one_or_all_of_doublePerp (d : S.LocalPolarFacts) {x y z : S.Point}
    (hxy : ¬ S.Collinear x y) (hxz : ¬ S.Collinear x z) (hyz : ¬ S.Collinear y z)
    (hz : z ∈ S.DoublePerp x y) : BinaryPolarGeometry.OneOrAll S.Collinear x y z := by
  let : Finite S.Point := Nat.finite_of_card_ne_zero (by rw [S.c3_points_card d]; decide)
  let A : Set S.Point := {u | S.Collinear x u}
  let B : Set S.Point := {u | S.Collinear y u}
  let C : Set S.Point := {u | S.Collinear z u}
  have hab : (A ∩ B).ncard = 15 := S.commonNeighbors_card d hxy
  have ha : A.ncard = 31 := S.closed_neighbors_card x
  have hb : B.ncard = 31 := S.closed_neighbors_card y
  have hc : C.ncard = 31 := S.closed_neighbors_card z
  have hac : A ∩ B = A ∩ C := S.commonNeighbors_eq_of_doublePerp d hxy hxz hz
  have hbc : A ∩ B = B ∩ C := by
    have h := S.commonNeighbors_eq_of_doublePerp d
      (fun h => hxy (S.collinear_symm h)) hyz (show z ∈ S.DoublePerp y x from fun u hu hv => hz u hv hu)
    have hh : B ∩ A = B ∩ C := h
    simpa only [Set.inter_comm B A] using hh
  have hi : (A ∪ B) ∩ C = A ∩ B := by
    rw [Set.union_inter_distrib_right, ← hac, ← hbc, Set.union_self]
  have hcount : (A ∪ B ∪ C).ncard = 63 := by
    have h1 := Set.ncard_union_add_ncard_inter A B
    have h2 := Set.ncard_union_add_ncard_inter (A ∪ B) C
    rw [ha, hb, hab] at h1
    rw [hi, hab, hc] at h2
    omega
  have huniv : A ∪ B ∪ C = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, S.c3_points_card d, hcount]
  intro w
  have hany : S.Collinear w x ∨ S.Collinear w y ∨ S.Collinear w z := by
    have h : w ∈ A ∪ B ∪ C := huniv ▸ Set.mem_univ w
    change (S.Collinear x w ∨ S.Collinear y w) ∨ S.Collinear z w at h
    rcases h with (h | h) | h
    · exact Or.inl (S.collinear_symm h)
    · exact Or.inr (Or.inl (S.collinear_symm h))
    · exact Or.inr (Or.inr (S.collinear_symm h))
  have habc : S.Collinear w x → S.Collinear w y → S.Collinear w z :=
    fun h1 h2 => S.collinear_symm (hz w (S.collinear_symm h1) (S.collinear_symm h2))
  have hacb : S.Collinear w x → S.Collinear w z → S.Collinear w y := by
    intro h1 h2
    have h : w ∈ A ∩ C := ⟨S.collinear_symm h1, S.collinear_symm h2⟩
    rw [← hac] at h
    exact S.collinear_symm h.2
  have hbca : S.Collinear w y → S.Collinear w z → S.Collinear w x := by
    intro h1 h2
    have h : w ∈ B ∩ C := ⟨S.collinear_symm h1, S.collinear_symm h2⟩
    rw [← hbc] at h
    exact S.collinear_symm h.1
  tauto

end Quasithin.I5.DSystem
