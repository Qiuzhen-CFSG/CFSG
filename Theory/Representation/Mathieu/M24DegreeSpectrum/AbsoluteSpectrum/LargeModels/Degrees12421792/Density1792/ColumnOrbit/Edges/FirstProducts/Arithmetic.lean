module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Contracts

/-!
# Sequential certificates for first-generator column products

An entry records a parent index, its packed input column and the packed output.
The increasing parent indices allow `checkInputs` to read the original columns
once. `checkOutputs` reads every published parent/actor and child together,
consuming exactly one entry for each first-generator edge. Their soundness
connects the separately checked raw-numeral products to `ProductsFor true`.

Source: ATLAS M24G1-f2r1792B0; attribution and conventions in
`../source/README.md`. The concrete application is `../FirstProducts.lean`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.FirstProducts

/-- Parent index, packed parent column, packed child column. -/
abbrev Entry := Nat × Nat × Nat

/-- Match increasing parent indices against a single scan of the columns. -/
def checkInputs : Nat → List Nat → List Entry → Bool
  | _, _, [] => true
  | _, [], _::_ => false
  | k, x::xs, e::es =>
    if e.1 == k then (x == e.2.1) && checkInputs (k+1) xs es
    else checkInputs (k+1) xs (e::es)

theorem checkInputs_sound (xs : List Nat) (k : Nat) (es : List Entry)
    (h : checkInputs k xs es = true) (e : Entry) (he : e ∈ es) :
    k ≤ e.1 ∧ xs[e.1-k]! = e.2.1 := by
  induction xs generalizing k es with
  | nil =>
    cases es with
    | nil => simp at he
    | cons a es => simp [checkInputs] at h
  | cons x xs ih =>
    cases es with
    | nil => simp at he
    | cons a es =>
      simp only [checkInputs] at h
      split at h
      next hk =>
        have hk : a.1 = k := by simpa using hk
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases List.mem_cons.mp he with rfl | he
        · simp [hk, h.1]
        · obtain ⟨hle, hget⟩ := ih (k+1) es h.2 he
          have hi : e.1-k = (e.1-(k+1))+1 := by omega
          exact ⟨by omega, by simpa [hi] using hget⟩
      next hk =>
        obtain ⟨hle, hget⟩ := ih (k+1) (a::es) h he
        have hi : e.1-k = (e.1-(k+1))+1 := by omega
        exact ⟨by omega, by simpa [hi] using hget⟩

/-- Cover all first-labelled edges in the published order, checking each child. -/
def checkOutputs : List (Nat × Bool) → List Nat → List Entry → Bool
  | [], [], [] => true
  | (_, false)::ps, _::ys, es => checkOutputs ps ys es
  | (p, true)::ps, y::ys, e::es =>
    (p == e.1) && (y == e.2.2) && checkOutputs ps ys es
  | _, _, _ => false

theorem checkOutputs_sound (ps : List (Nat × Bool)) (ys : List Nat)
    (es : List Entry) (h : checkOutputs ps ys es = true)
    (i : Nat) (hi : i < ps.length) (hb : ps[i]!.2 = true) :
    ∃ e ∈ es, e.1 = ps[i]!.1 ∧ e.2.2 = ys[i]! := by
  induction ps generalizing ys es i with
  | nil => simp at hi
  | cons a ps ih =>
    cases ys with
    | nil => simp [checkOutputs] at h
    | cons y ys =>
      rcases a with ⟨p, b⟩
      cases b with
      | false =>
        cases i with
        | zero => simp at hb
        | succ i =>
          exact ih ys es h i (by simpa using hi) (by simpa using hb)
      | true =>
        cases es with
        | nil => simp [checkOutputs] at h
        | cons e es =>
          simp only [checkOutputs, Bool.and_eq_true, beq_iff_eq] at h
          cases i with
          | zero => exact ⟨e, by simp, by simpa using h.1.1.symm,
              by simpa using h.1.2.symm⟩
          | succ i =>
            obtain ⟨a, ha, hp, hy⟩ := ih ys es h.2 i
              (by simpa using hi) (by simpa using hb)
            exact ⟨a, List.mem_cons_of_mem e ha, hp, hy⟩

/-- The actual numerical products, independent of all indexing conventions. -/
def checkProducts (es : List Entry) : Bool :=
  es.all (fun e => select firstTranspose e.2.1 == e.2.2)

theorem checkProducts_append (xs ys : List Entry) :
    checkProducts (xs ++ ys) = (checkProducts xs && checkProducts ys) :=
  List.all_append

/-- Discharge the literal numerical contract consumed by `column_step_of_certificates`. -/
theorem productsFor_of_checks (es : List Entry)
    (hin : checkInputs 0 ColumnData.columns es = true)
    (hout : checkOutputs ColumnData.parents ColumnData.columns.tail es = true)
    (hprod : checkProducts es = true) : ProductsFor true := by
  intro i hi
  obtain ⟨e, he, hp, hy⟩ := checkOutputs_sound _ _ _ hout i.val
    (by simpa only [ColumnData.parents_length] using i.isLt) hi
  have hx := (checkInputs_sound _ _ _ hin e he).2
  have hm := List.all_eq_true.mp hprod e he
  have ht : ColumnData.columns.tail[i.val]! = ColumnData.columns[i.val+1]! := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_tail]
  simpa only [ColumnData.parent, ColumnData.parentIndex, Nat.sub_zero,
    Fin.val_succ, if_true, hp, hy, ht, beq_iff_eq] using
      (show select firstTranspose ColumnData.columns[e.1]! = e.2.2 by
        rw [show ColumnData.columns[e.1]! = e.2.1 from by simpa using hx]
        simpa using hm)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.FirstProducts
