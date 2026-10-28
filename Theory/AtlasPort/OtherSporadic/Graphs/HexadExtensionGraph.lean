/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Graphs/HexadExtensionGraph.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Combinatorics.HexadIntersectionCounts
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# HexadExtensionGraph

The hexad extension adjoins a base vertex to 22 points and 77 hexads.
Incidence joins points to hexads, and disjointness joins pairs of hexads.
Partitioning neighbors by these three vertex types reduces their counts to
the point, pair, and disjointness identities of a hexad design.

Source: Gerald Höhn, ATLAS, `Atlas/Graphs/HexadExtensionGraph.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
The construction and counting use only SimpleGraph.Basic; strong regularity is separate.
Definition bodies remain exposed for downstream calculations in the source API.
-/

set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Graphs
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

abbrev HexadExtensionVertices (blocks : Finset (Finset V)) := Unit ⊕ (V ⊕ {B // B ∈ blocks})

def hexadExtensionAdj (blocks : Finset (Finset V)) :
    HexadExtensionVertices blocks → HexadExtensionVertices blocks → Prop
  | Sum.inl _, Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inl _), Sum.inl _ => True
  | Sum.inr (Sum.inl j), Sum.inr (Sum.inr B) => j ∈ B.val
  | Sum.inr (Sum.inr B), Sum.inr (Sum.inl j) => j ∈ B.val
  | Sum.inr (Sum.inr B), Sum.inr (Sum.inr C) => (B.val ∩ C.val).card = 0
  | _, _ => False

def hexadExtensionGraph (blocks : Finset (Finset V)) (h : HexadDesignData blocks) :
    SimpleGraph (HexadExtensionVertices blocks) where
  Adj := hexadExtensionAdj blocks
  symm := ⟨by
    intro x y hxy
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    all_goals try exact hxy
    change (y.val ∩ x.val).card = 0
    rw [Finset.inter_comm]; exact hxy⟩
  loopless := ⟨by
    intro x hx
    rcases x with x | (x | x)
    · exact hx
    · exact hx
    · change (x.val ∩ x.val).card = 0 at hx
      rw [Finset.inter_self,h.size x.val x.prop] at hx
      omega⟩

theorem hexad_extension_pred_card (blocks : Finset (Finset V))
    (P : HexadExtensionVertices blocks → Prop) :
    Nat.card {x // P x} = (if P (Sum.inl ()) then 1 else 0)+
      Nat.card {x : V // P (Sum.inr (Sum.inl x))}+
      Nat.card {B : {B // B ∈ blocks} // P (Sum.inr (Sum.inr B))} := by
  rw [Nat.card_congr Equiv.subtypeSum,Nat.card_sum,Nat.card_congr Equiv.subtypeSum,Nat.card_sum]
  have hu : Nat.card {u : Unit // P (Sum.inl u)} = if P (Sum.inl ()) then 1 else 0 := by
    have hP (u : Unit) : P (Sum.inl u) ↔ P (Sum.inl ()) := by cases u; rfl
    simp_rw [hP]
    by_cases hp : P (Sum.inl ()) <;> simp [hp]
  rw [hu]
  omega

theorem block_subtype_pred_card (blocks : Finset (Finset V)) (P : Finset V → Prop) :
    Nat.card {B : {B // B ∈ blocks} // P B.val} = (blocks.filter P).card := by
  let e : {B : {B // B ∈ blocks} // P B.val} ≃ {B // B ∈ blocks.filter P} := {
    toFun B := ⟨B.val.val,Finset.mem_filter.mpr ⟨B.val.prop,B.prop⟩⟩
    invFun B := ⟨⟨B.val,(Finset.mem_filter.mp B.prop).1⟩,(Finset.mem_filter.mp B.prop).2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem point_subtype_mem_card (B : Finset V) : Nat.card {j : V // j ∈ B} = B.card := by
  rw [Nat.card_eq_fintype_card,Fintype.card_coe]

private theorem nat_card_false (A : Type*) : Nat.card {_a : A // False} = 0 := by simp
private theorem nat_card_true (A : Type*) [Finite A] : Nat.card {_a : A // True} = Nat.card A := by simp

theorem hexad_extension_neighbor_card (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (hv : Nat.card V = 22) (x : HexadExtensionVertices blocks) :
    Nat.card {y // (hexadExtensionGraph blocks h).Adj x y} = 22 := by
  rw [hexad_extension_pred_card]
  rcases x with x | (x | x)
  · dsimp +instances only [hexadExtensionGraph, hexadExtensionAdj]
    simp only [if_false, nat_card_false, nat_card_true, zero_add, add_zero, hv]
  · dsimp +instances only [hexadExtensionGraph, hexadExtensionAdj]
    rw [if_true, nat_card_false, add_zero,
      block_subtype_pred_card blocks (fun B => x ∈ B)]
    convert (show 1 + 21 = 22 by decide) using 1
    congr 1
    convert h.point x using 1
    congr 1
    ext E
    simp only [Finset.mem_filter]
  · dsimp +instances only [hexadExtensionGraph, hexadExtensionAdj]
    rw [if_false, zero_add, point_subtype_mem_card,
      block_subtype_pred_card blocks (fun B => (x.val ∩ B).card = 0),
      h.size x.val x.prop]
    convert (show 6 + 16 = 22 by decide) using 1
    congr 1
    convert hexad_disjoint_card blocks h x.val x.prop using 1
    congr 1
    ext E
    simp only [Finset.mem_filter]

theorem hexad_extension_base_common (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (y : HexadExtensionVertices blocks) (hy : y ≠ Sum.inl ()) :
    Nat.card {z // (hexadExtensionGraph blocks h).Adj (Sum.inl ()) z ∧
      (hexadExtensionGraph blocks h).Adj y z} =
      if (hexadExtensionGraph blocks h).Adj (Sum.inl ()) y then 0 else 6 := by
  rw [hexad_extension_pred_card]
  rcases y with y | (y | y)
  · exact False.elim (hy rfl)
  · simp [hexadExtensionGraph,hexadExtensionAdj]
  · simp [hexadExtensionGraph,hexadExtensionAdj,h.size y.val y.prop]

theorem hexad_extension_points_common (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (b c : V) (hbc : b ≠ c) :
    Nat.card {z // (hexadExtensionGraph blocks h).Adj (Sum.inr (Sum.inl b)) z ∧
      (hexadExtensionGraph blocks h).Adj (Sum.inr (Sum.inl c)) z} = 6 := by
  rw [hexad_extension_pred_card]
  simp only [hexadExtensionGraph,hexadExtensionAdj,and_self,ite_true,nat_card_false,add_zero,
    block_subtype_pred_card blocks (fun B => b ∈ B ∧ c ∈ B)]
  have hc := h.pair b c hbc
  convert (show 1 + 5 = 6 by decide) using 1
  congr 1
  convert hc using 1
  congr 1
  ext E
  simp only [Finset.mem_filter]

theorem hexad_extension_point_block_common (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (j : V) (B : {B // B ∈ blocks}) :
    Nat.card {z // (hexadExtensionGraph blocks h).Adj (Sum.inr (Sum.inl j)) z ∧
      (hexadExtensionGraph blocks h).Adj (Sum.inr (Sum.inr B)) z} =
      if j ∈ B.val then 0 else 6 := by
  rw [hexad_extension_pred_card]
  simp only [hexadExtensionGraph,hexadExtensionAdj,and_false,false_and,
    ite_false,nat_card_false,zero_add]
  rw [block_subtype_pred_card blocks (fun E => j ∈ E ∧ (B.val ∩ E).card = 0)]
  by_cases hj : j ∈ B.val
  · rw [if_pos hj]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro E hE
    have hE' : E ∈ blocks ∧ j ∈ E ∧ (B.val ∩ E).card = 0 := by
      simpa only [Finset.mem_filter] using hE
    obtain ⟨_,hjE,hBE⟩ := hE'
    have hm : j ∈ B.val ∩ E := Finset.mem_inter.mpr ⟨hj,hjE⟩
    rw [Finset.card_eq_zero.mp hBE] at hm
    exact Finset.notMem_empty j hm
  · rw [if_neg hj]
    convert hexad_point_disjoint_card blocks h B.val B.prop j hj using 1
    congr 1
    ext E
    simp only [Finset.mem_filter]

theorem hexad_extension_blocks_common (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (B C : {B // B ∈ blocks}) (hBC : B ≠ C) :
    Nat.card {z // (hexadExtensionGraph blocks h).Adj (Sum.inr (Sum.inr B)) z ∧
      (hexadExtensionGraph blocks h).Adj (Sum.inr (Sum.inr C)) z} =
      if (B.val ∩ C.val).card = 0 then 0 else 6 := by
  rw [hexad_extension_pred_card]
  simp only [hexadExtensionGraph,hexadExtensionAdj,false_and,ite_false,
    zero_add]
  have he : {j : V // j ∈ B.val ∧ j ∈ C.val} ≃ {j // j ∈ B.val ∩ C.val} :=
    Equiv.subtypeEquivRight (fun j => Finset.mem_inter.symm)
  rw [Nat.card_congr he,
    point_subtype_mem_card,block_subtype_pred_card blocks (fun E => (B.val ∩ E).card = 0 ∧ (C.val ∩ E).card = 0)]
  have hi := h.intersection B.val B.prop C.val C.prop (fun he => hBC (Subtype.ext he))
  have hc := hexad_common_disjoint_card blocks h B.val C.val B.prop C.prop
    (fun he => hBC (Subtype.ext he))
  have ha : (B.val ∩ C.val).card + 2*(B.val ∩ C.val).card =
      if (B.val ∩ C.val).card = 0 then 0 else 6 := by
    rcases hi with hi | hi <;> simp [hi]
  convert ha using 1
  congr 1
  convert hc using 1
  congr 1
  ext E
  simp only [Finset.mem_filter]
end Atlas.Graphs
