module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Contracts

/-!
# Connecting literal second-generator products to the published tree

`checkLinks` scans the child columns and labelled parents together. For a
second-labelled edge it advances a cursor through the original column list
and matches the next certified input/output pair. The checked cursor inequality
makes the scan sound without repeatedly indexing the full column list.
`productsFor_of_checks` applies that soundness to the exact `ProductsFor false`
contract. The numerical checks are in the sibling batch modules and assembly.

Source: `../source/README.md` and `source/README.md`; the unchanged ATLAS
M24G1-f2r1792B0 candidate columns and parent tree.
-/

@[expose] public section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.SecondProducts

def checkLinks : List (Nat × Bool) → List Nat → List Nat → Nat → List (Nat × Nat) → Bool
  | [], _, _, _, _ => true
  | _ :: _, [], _, _, _ => false
  | p :: ps, y :: ys, xs, cursor, cert =>
    if p.2 then checkLinks ps ys xs cursor cert
    else match cert with
    | [] => false
    | q :: qs =>
      let zs := xs.drop (p.1 - cursor)
      decide (cursor ≤ p.1) && (zs[0]! == q.1) && (y == q.2) &&
        checkLinks ps ys zs p.1 qs

theorem checkLinks_sound (cols : List Nat) (ps : List (Nat × Bool))
    (ys xs : List Nat) (cursor : Nat) (cert : List (Nat × Nat))
    (hx : xs = cols.drop cursor) (h : checkLinks ps ys xs cursor cert = true)
    (i : Nat) (hi : i < ps.length) (hb : ps[i]!.2 = false) :
    (cols[ps[i]!.1]!, ys[i]!) ∈ cert := by
  induction ps generalizing ys xs cursor cert i with
  | nil => simp at hi
  | cons p ps ih =>
    cases ys with
    | nil => simp [checkLinks] at h
    | cons y ys =>
      cases hp : p.2 with
      | true =>
        simp only [checkLinks, hp, ↓reduceIte] at h
        cases i with
        | zero => simp [hp] at hb
        | succ i =>
          exact ih ys xs cursor cert hx h i (by simpa using hi) (by simpa using hb)
      | false =>
        cases cert with
        | nil => simp [checkLinks, hp] at h
        | cons q qs =>
          simp only [checkLinks, hp, Bool.false_eq_true, ↓reduceIte,
            Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          have hz : xs.drop (p.1 - cursor) = cols.drop p.1 := by
            rw [hx, List.drop_drop]
            congr 1
            omega
          have ha : cols[p.1]! = q.1 := by
            have hh := h.1.1.2
            rw [hz] at hh
            simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_drop,
              Nat.add_zero] using hh
          cases i with
          | zero =>
            simp only [List.getElem!_cons_zero, ha, h.1.2]
            exact List.mem_cons_self
          | succ i =>
            exact List.mem_cons_of_mem q
              (ih ys (xs.drop (p.1 - cursor)) p.1 qs hz h.2 i
                (by simpa using hi) (by simpa using hb))


/-- A complete link scan and checked products discharge the literal edge contract. -/
theorem productsFor_of_checks (cert : List (Nat × Nat))
    (hc : checkLinks ColumnData.parents (ColumnData.columns.drop 1)
      ColumnData.columns 0 cert = true)
    (hp : cert.all (fun p => select secondTranspose p.1 == p.2) = true) :
    ProductsFor false := by
  intro i hi
  have hm := checkLinks_sound ColumnData.columns ColumnData.parents
    (ColumnData.columns.drop 1) ColumnData.columns 0 cert
    (by rw [List.drop_zero]) hc i.val
    (by simpa only [ColumnData.parents_length] using i.isLt) hi
  have he := List.all_eq_true.mp hp _ hm
  simp only [beq_iff_eq] at he
  change select secondTranspose ColumnData.columns[(ColumnData.parent i).val]! =
    ColumnData.columns[i.succ.val]!
  simpa only [ColumnData.parent, ColumnData.parentIndex,
    List.getElem!_eq_getElem?_getD, List.getElem?_drop, Fin.val_succ,
    Nat.add_comm] using he

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.SecondProducts
