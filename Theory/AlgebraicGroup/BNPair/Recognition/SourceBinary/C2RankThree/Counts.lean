module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.CosetAction
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.BruhatCoordinates
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# The actual C₂ coset degree from Bruhat coordinates

For m=4, the eight alternating Weyl words enumerate the actual marked
Weyl group. Refined Bruhat coordinates give each cell order |B| q^length.
Their disjoint union gives |Y| = |B|(1+2q+2q²+2q³+q⁴). Dividing by
the actual parabolic order |B|(q+1) gives the coset degree
q³+q²+q+1 for either endpoint. This includes q=2 without assuming a
model isomorphism or a classical-group order formula.

This calculation removes the total-degree premise of the source
incidence application. The three parabolic suborbits and their individual
sizes are separate obligations, not consequences asserted from this count.

Source: Fong–Seitz I (1H)–(1I), pp.5–6; Carter 2.5.10–2.5.17,
the supplied GLS3 Chapter2Ca2.tex, specialized to m=4.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private def weylWord : Fin 8 → Weyl Q :=
  ![alternatingWord Q false 0, alternatingWord Q false 1, alternatingWord Q true 1,
    alternatingWord Q false 2, alternatingWord Q true 2, alternatingWord Q false 3,
    alternatingWord Q true 3, alternatingWord Q false 4]

private theorem weylWord_surjective (hm : rotationOrder Q = 4) :
    Function.Surjective (weylWord Q) := by
  intro w
  obtain ⟨b,n,hn,rfl⟩ := exists_alternatingWord Q w
  rw [hm] at hn
  interval_cases n <;> cases b
  · exact ⟨0,rfl⟩
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · refine ⟨7,?_⟩
    change alternatingWord Q false 4 = alternatingWord Q true 4
    rw [← hm,alternatingWord_longest,alternatingWord_longest]

private theorem weylWord_injective (hm : rotationOrder Q = 4) :
    Function.Injective (weylWord Q) := by
  exact ((weylWord_surjective Q hm).bijective_of_nat_card_le (by
    rw [Nat.card_fin,weyl_card,hm])).1

/-- Refined Bruhat coordinates count each actual cell from the root orders. -/
theorem cell_card_of_equal_roots {q : ℕ}
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) (w : Weyl Q) :
    Nat.card (Q.tits.bruhatCell w) = Nat.card Q.tits.B * q^(Q.tits.wordLength w) := by
  have hcoord := Nat.card_congr (bruhatCoordinates Q split w (representative w)
    (representative_spec w))
  rw [Nat.card_prod] at hcoord
  rw [← hcoord]
  congr 1
  obtain ⟨b,n,hn,he⟩ := exists_alternatingWord Q w⁻¹
  have hc := rootIntersection_card_alternating Q split b n hn
  rw [he,inv_inv,alternatingOrder_eq_pow Q split (hq0.trans hq1.symm),hq0] at hc
  have hl := congrArg Q.tits.wordLength he
  rw [wordLength_alternatingWord Q b hn,wordLength_inv] at hl
  exact hc.trans (congrArg (q^·) hl)

/-- The sum of the eight actual Bruhat cells, for m=4. -/
theorem quotient_card_of_equal_roots {q : ℕ} (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (X ⧸ Q.D) = Nat.card Q.tits.B * (1+2*q+2*q^2+2*q^3+q^4) := by
  classical
  have hcover : (⋃ i : Fin 8, Q.tits.bruhatCell (weylWord Q i)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨w,hw⟩ := Q.tits.exists_mem_doubleCoset g
    obtain ⟨i,rfl⟩ := weylWord_surjective Q hm w
    exact Set.mem_iUnion.mpr ⟨i,hw⟩
  have hd : Pairwise (fun i j : Fin 8 =>
      Disjoint (Q.tits.bruhatCell (weylWord Q i)) (Q.tits.bruhatCell (weylWord Q j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro g hi hj
    exact hij (weylWord_injective Q hm (Q.tits.doubleCoset_index_unique hi hj))
  have hc := Set.ncard_iUnion_of_finite
    (fun i : Fin 8 => Set.toFinite (Q.tits.bruhatCell (weylWord Q i))) hd
  rw [hcover,Set.ncard_univ] at hc
  rw [hc,finsum_eq_sum_of_fintype]
  change (∑ i : Fin 8, Nat.card (Q.tits.bruhatCell (weylWord Q i))) = _
  simp_rw [cell_card_of_equal_roots Q split hq0 hq1]
  have hlen (b : Bool) (n : ℕ) (hn : n ≤ 4) :
      Q.tits.wordLength (alternatingWord Q b n) = n :=
    wordLength_alternatingWord Q b (hm.symm ▸ hn)
  simp only [weylWord,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
    hlen false 0 (by omega), hlen false 1 (by omega), hlen true 1 (by omega),
    hlen false 2 (by omega), hlen true 2 (by omega),
    hlen false 3 (by omega), hlen true 3 (by omega), hlen false 4 (by omega)]
  ring

/-- The degree of either original parabolic coset action, derived from its
literal Bruhat cells and endpoint index, not from a model-group order. -/
theorem points_card {q : ℕ} (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) (i : Fin 2) :
    Nat.card (Points Q i) = q^3+q^2+q+1 := by
  let H := Q.tits.standardParabolic {Q.simple i}
  have hqi : Nat.card (simpleRoot Q split i) = q := by fin_cases i <;> assumption
  have hi := singleton_parabolic_root_index Q split i
  rw [hqi] at hi
  have hH : Nat.card H = Nat.card Q.tits.B * (1+q) := by
    have hh := (Q.tits.B.subgroupOf H).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (Q.tits.B_le_standardParabolic _)).toEquiv,hi] at hh
    exact hh.symm
  change H.index = _
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
  rw [H.card_mul_index,quotient_card_of_equal_roots Q split hm hq0 hq1,hH]
  ring

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
