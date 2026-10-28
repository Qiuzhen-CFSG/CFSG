module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Counts

/-!
# The three actual C₂ parabolic double cosets

A singleton-parabolic double coset is the union of its four possible Weyl
cells; this follows from exchange on both sides. For dihedral parameter
four, the eight distinct Weyl words partition into sets of sizes two,
four and two. Thus the opposite double coset is exactly the complement
of the base parabolic and the neighboring double coset.

Refined Bruhat coordinates count the neighboring cells as
|B|(q+2q²+q³) and the opposite cells as |B|(q³+q⁴). All groups and
representatives belong to the original marked quotient. The proof uses
no model-group order, simplicity, or recognition premise, and includes q=2.
Passage from these sets to the source suborbits is in `Suborbits`.

Source: Fong–Seitz I (1I), pp.5–6; II (7C), p.193;
Carter §2.5, Bruhat decomposition and exchange.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
variable {X : Type*} [Group X] {T : TitsSystem (X := X)}

private theorem cell_inv {w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N}
    {x : X} (hx : x ∈ T.bruhatCell w) : x⁻¹ ∈ T.bruhatCell w⁻¹ := by
  obtain ⟨n,hn⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) w
  rw [bruhatCell,B_mul_representativeSet_mul_B T.B T.N w n hn] at hx
  rw [bruhatCell,B_mul_representativeSet_mul_B T.B T.N w⁻¹ n⁻¹ (by rw [map_inv,hn])]
  obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  exact DoubleCoset.mem_doubleCoset.mpr ⟨b⁻¹,T.B.inv_mem hb,a⁻¹,T.B.inv_mem ha,by
    simp only [coe_inv,mul_inv_rev,mul_assoc]⟩

private theorem cell_mul_simple {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N}
    (hs : s ∈ T.S) (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    T.bruhatCell w * T.bruhatCell s ⊆ T.bruhatCell (w*s) ∪ T.bruhatCell w := by
  have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (T.involutions s hs).2)
  rintro _ ⟨a,ha,b,hb,rfl⟩
  have hb' : b⁻¹ ∈ T.bruhatCell s := by simpa only [hi] using cell_inv hb
  rcases doubleCoset_mul_doubleCoset_subset_of_mem_S T hs w⁻¹
    ⟨b⁻¹,hb',a⁻¹,cell_inv ha,rfl⟩ with h | h
  · exact Or.inl (by simpa only [mul_inv_rev,inv_inv,hi] using cell_inv h)
  · exact Or.inr (by simpa only [mul_inv_rev,inv_inv] using cell_inv h)

/-- A singleton-parabolic double coset has exactly its four possible Weyl cells.
Repeated cells in this formula are intentional. -/
theorem parabolic_doubleCoset_cells
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (n : T.N)
    (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = w) :
    DoubleCoset.doubleCoset (n : X) (T.standardParabolic {s}) (T.standardParabolic {s}) =
      (T.bruhatCell w ∪ T.bruhatCell (s*w)) ∪
      (T.bruhatCell (w*s) ∪ T.bruhatCell (s*w*s)) := by
  let H := T.standardParabolic {s}
  let D := DoubleCoset.doubleCoset (n : X) H H
  have hB : T.B ≤ H := T.B_le_standardParabolic _
  have hS : T.bruhatCell s ⊆ H := by
    intro x hx
    rw [show (H : Set X) = (T.B : Set X) ∪ T.bruhatCell s from singleton_parabolic_cells hs]
    exact Or.inr hx
  have hw : T.bruhatCell w ⊆ D := by
    rw [bruhatCell,B_mul_representativeSet_mul_B T.B T.N w n hn]
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact DoubleCoset.mem_doubleCoset.mpr ⟨a,hB ha,b,hB hb,rfl⟩
  have hl {x y : X} (hx : x ∈ H) (hy : y ∈ D) : x*y ∈ D := by
    obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    exact DoubleCoset.mem_doubleCoset.mpr ⟨x*a,H.mul_mem hx ha,b,hb,by simp only [mul_assoc]⟩
  have hr {x y : X} (hx : x ∈ D) (hy : y ∈ H) : x*y ∈ D := by
    obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact DoubleCoset.mem_doubleCoset.mpr ⟨a,ha,b*y,H.mul_mem hb hy,by simp only [mul_assoc]⟩
  have hsw : T.bruhatCell (s*w) ⊆ D := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := T.bruhatCell_mul_subset_product s w hx
    exact hl (hS ha) (hw hb)
  have hws : T.bruhatCell (w*s) ⊆ D := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := T.bruhatCell_mul_subset_product w s hx
    exact hr (hw ha) (hS hb)
  have hsws : T.bruhatCell (s*w*s) ⊆ D := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := T.bruhatCell_mul_subset_product (s*w) s hx
    exact hr (hsw ha) (hS hb)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    have han : a*(n : X) ∈ T.bruhatCell w ∪ T.bruhatCell (s*w) := by
      rw [show (H : Set X) = (T.B : Set X) ∪ T.bruhatCell s from singleton_parabolic_cells hs] at ha
      rcases ha with ha | ha
      · exact Or.inl (by simpa only [bruhatCell,mul_one] using
          mul_mem_doubleCoset T.B T.N w ha T.B.one_mem (T.representative_mem_bruhatCell w n hn))
      · exact (doubleCoset_mul_doubleCoset_subset_of_mem_S T hs w
          ⟨a,ha,n,T.representative_mem_bruhatCell w n hn,rfl⟩).symm
    rw [show (H : Set X) = (T.B : Set X) ∪ T.bruhatCell s from singleton_parabolic_cells hs] at hb
    rcases hb with hb | hb
    · rcases han with han | han
      · exact Or.inl (Or.inl (by
          simpa only [bruhatCell,one_mul] using mul_mem_doubleCoset T.B T.N w T.B.one_mem hb han))
      · exact Or.inl (Or.inr (by
          simpa only [bruhatCell,one_mul] using mul_mem_doubleCoset T.B T.N (s*w) T.B.one_mem hb han))
    · rcases han with han | han
      · rcases cell_mul_simple hs w ⟨_,han,b,hb,rfl⟩ with hh | hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inl (Or.inl hh)
      · rcases cell_mul_simple hs (s*w) ⟨_,han,b,hb,rfl⟩ with hh | hh
        · exact Or.inr (Or.inr hh)
        · exact Or.inl (Or.inr hh)
  · rintro x ((hx | hx) | (hx | hx))
    · exact hw hx
    · exact hsw hx
    · exact hws hx
    · exact hsws hx

variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)

/-- The eight Weyl words ordered by their second-parabolic double cosets. -/
@[expose] def cosetWord : Fin 8 → Weyl Q :=
  ![alternatingWord Q false 0, alternatingWord Q true 1,
    alternatingWord Q false 1, alternatingWord Q true 2,
    alternatingWord Q false 2, alternatingWord Q true 3,
    alternatingWord Q false 3, alternatingWord Q false 4]

theorem cosetWord_surjective (hm : rotationOrder Q = 4) :
    Function.Surjective (cosetWord Q) := by
  intro w
  obtain ⟨b,n,hn,rfl⟩ := exists_alternatingWord Q w
  rw [hm] at hn
  interval_cases n <;> cases b
  · exact ⟨0,rfl⟩
  · exact ⟨0,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨7,rfl⟩
  · refine ⟨7,?_⟩
    change alternatingWord Q false 4 = alternatingWord Q true 4
    rw [← hm,alternatingWord_longest,alternatingWord_longest]

theorem cosetWord_injective (hm : rotationOrder Q = 4) :
    Function.Injective (cosetWord Q) :=
  ((cosetWord_surjective Q hm).bijective_of_nat_card_le (by
    rw [Nat.card_fin,weyl_card,hm])).1

/-- The neighboring suborbit lifts to four distinct Bruhat cells. -/
theorem neighbor_doubleCoset_cells :
    DoubleCoset.doubleCoset (representative (Q.simple 0) : X ⧸ Q.D)
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.standardParabolic {Q.simple 1}) =
      ⋃ i : Fin 4, Q.tits.bruhatCell (cosetWord Q ⟨i.val+2,by omega⟩) := by
  rw [parabolic_doubleCoset_cells (Q.simple_mem 1) _ _ (representative_spec _)]
  ext x
  simp only [Set.mem_iUnion,Set.mem_union,Fin.exists_fin_succ]
  simp only [cosetWord, Fin.val_zero,
    Fin.val_succ, Nat.reduceAdd, Matrix.cons_val_zero',Matrix.cons_val_succ',
    alternatingWord,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,
    mul_one,mul_assoc,IsEmpty.exists_iff,or_false]
  tauto

/-- The opposite suborbit lifts to the final two Bruhat cells. -/
theorem opposite_doubleCoset_cells (hm : rotationOrder Q = 4) :
    DoubleCoset.doubleCoset (representative (longest Q) : X ⧸ Q.D)
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.standardParabolic {Q.simple 1}) =
      ⋃ i : Fin 2, Q.tits.bruhatCell (cosetWord Q ⟨i.val+6,by omega⟩) := by
  have hbraid : Q.simple 0*Q.simple 1*Q.simple 0*Q.simple 1 =
      Q.simple 1*Q.simple 0*Q.simple 1*Q.simple 0 := by
    have h := (alternatingWord_longest Q false).trans (alternatingWord_longest Q true).symm
    simpa only [hm,alternatingWord,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_false,Bool.not_true,mul_one,mul_assoc] using h
  have h0 : Q.simple 0*Q.simple 0 = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 0)).2
  have h1 : Q.simple 1*Q.simple 1 = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 1)).2
  have hlong : longest Q = Q.simple 0*Q.simple 1*Q.simple 0*Q.simple 1 := by
    simpa only [hm,alternatingWord,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_false,Bool.not_true,mul_one,mul_assoc] using (alternatingWord_longest Q false).symm
  have hleft : Q.simple 1*longest Q = Q.simple 0*Q.simple 1*Q.simple 0 := by
    rw [hlong,hbraid,← mul_assoc,← mul_assoc,← mul_assoc,h1,one_mul]
  have hright : longest Q*Q.simple 1 = Q.simple 0*Q.simple 1*Q.simple 0 := by
    rw [hlong,mul_assoc _ (Q.simple 1),h1,mul_one]
  have hboth : Q.simple 1*longest Q*Q.simple 1 = longest Q := by rw [hleft,hlong]
  rw [parabolic_doubleCoset_cells (Q.simple_mem 1) _ _ (representative_spec _),
    hboth,hleft,hright,hlong]
  ext x
  simp only [Set.mem_iUnion,Set.mem_union,Fin.exists_fin_succ]
  simp only [cosetWord,Fin.val_zero,
    Fin.val_succ,Nat.reduceAdd,Matrix.cons_val_zero',Matrix.cons_val_succ',
    alternatingWord,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,
    mul_one,mul_assoc,IsEmpty.exists_iff,or_false]
  tauto

private theorem cell_disjoint (hm : rotationOrder Q = 4) {i j : Fin 8} (hij : i ≠ j) :
    Disjoint (Q.tits.bruhatCell (cosetWord Q i)) (Q.tits.bruhatCell (cosetWord Q j)) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (cosetWord_injective Q hm (Q.tits.doubleCoset_index_unique hi hj))

/-- Counting the four neighboring cells before passage to cosets. -/
theorem neighbor_doubleCoset_card (split : SplitData Q.tits) {q : ℕ}
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (DoubleCoset.doubleCoset (representative (Q.simple 0) : X ⧸ Q.D)
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.standardParabolic {Q.simple 1})) =
      Nat.card Q.tits.B * (q+2*q^2+q^3) := by
  change (DoubleCoset.doubleCoset _ _ _).ncard = _
  rw [neighbor_doubleCoset_cells]
  have hd : Pairwise (fun i j : Fin 4 =>
      Disjoint (Q.tits.bruhatCell (cosetWord Q ⟨i.val+2,by omega⟩))
        (Q.tits.bruhatCell (cosetWord Q ⟨j.val+2,by omega⟩))) := by
    intro i j hij
    exact cell_disjoint Q hm (by intro he; exact hij (Fin.ext (Nat.add_right_cancel (congrArg Fin.val he))))
  rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) hd, finsum_eq_sum_of_fintype]
  change (∑ i : Fin 4, Nat.card (Q.tits.bruhatCell (cosetWord Q ⟨i.val+2,by omega⟩))) = _
  simp_rw [cell_card_of_equal_roots Q split hq0 hq1]
  have hlen (b : Bool) (n : ℕ) (hn : n ≤ 4) :
      Q.tits.wordLength (alternatingWord Q b n) = n :=
    wordLength_alternatingWord Q b (hm.symm ▸ hn)
  simp only [cosetWord,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.sum_univ_zero,
    hlen false 1 (by omega),hlen true 2 (by omega),hlen false 2 (by omega),
    hlen true 3 (by omega)]
  ring

/-- Counting the opposite cells before passage to cosets. -/
theorem opposite_doubleCoset_card (split : SplitData Q.tits) {q : ℕ}
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (DoubleCoset.doubleCoset (representative (longest Q) : X ⧸ Q.D)
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.standardParabolic {Q.simple 1})) =
      Nat.card Q.tits.B * (q^3+q^4) := by
  change (DoubleCoset.doubleCoset _ _ _).ncard = _
  rw [opposite_doubleCoset_cells Q hm]
  have hd : Pairwise (fun i j : Fin 2 =>
      Disjoint (Q.tits.bruhatCell (cosetWord Q ⟨i.val+6,by omega⟩))
        (Q.tits.bruhatCell (cosetWord Q ⟨j.val+6,by omega⟩))) := by
    intro i j hij
    exact cell_disjoint Q hm (by intro he; exact hij (Fin.ext (Nat.add_right_cancel (congrArg Fin.val he))))
  rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) hd, finsum_eq_sum_of_fintype]
  change (∑ i : Fin 2, Nat.card (Q.tits.bruhatCell (cosetWord Q ⟨i.val+6,by omega⟩))) = _
  simp_rw [cell_card_of_equal_roots Q split hq0 hq1]
  have hlen (b : Bool) (n : ℕ) (hn : n ≤ 4) :
      Q.tits.wordLength (alternatingWord Q b n) = n :=
    wordLength_alternatingWord Q b (hm.symm ▸ hn)
  simp only [cosetWord,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.sum_univ_zero,
    hlen false 3 (by omega),hlen false 4 (by omega)]
  ring

/-- The fixed suborbit lifts to the first two Weyl cells. -/
theorem base_parabolic_cells :
    (Q.tits.standardParabolic {Q.simple 1} : Set (X ⧸ Q.D)) =
      ⋃ i : Fin 2, Q.tits.bruhatCell (cosetWord Q ⟨i.val,by omega⟩) := by
  rw [singleton_parabolic_cells (Q.simple_mem 1)]
  ext x
  simp only [Set.mem_iUnion,Set.mem_union,Fin.exists_fin_succ]
  simp [cosetWord,alternatingWord]

/-- The opposite double coset is exactly the complement of the other two.
This proves the three-orbit assertion independently of their orders. -/
theorem opposite_doubleCoset_eq_compl (hm : rotationOrder Q = 4) :
    DoubleCoset.doubleCoset (representative (longest Q) : X ⧸ Q.D)
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.standardParabolic {Q.simple 1}) =
      ((Q.tits.standardParabolic {Q.simple 1} : Set (X ⧸ Q.D)) ∪
        DoubleCoset.doubleCoset (representative (Q.simple 0) : X ⧸ Q.D)
          (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.standardParabolic {Q.simple 1}))ᶜ := by
  ext x
  obtain ⟨w,hw⟩ := Q.tits.exists_mem_doubleCoset x
  obtain ⟨i,rfl⟩ := cosetWord_surjective Q hm w
  have hmem (j : Fin 8) : x ∈ Q.tits.bruhatCell (cosetWord Q j) ↔ j = i := by
    constructor
    · intro hj
      exact cosetWord_injective Q hm (Q.tits.doubleCoset_index_unique hj hw)
    · rintro rfl
      exact hw
  rw [opposite_doubleCoset_cells Q hm,neighbor_doubleCoset_cells Q,base_parabolic_cells Q]
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_iUnion,hmem]
  fin_cases i <;> simp [Fin.exists_fin_succ]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
