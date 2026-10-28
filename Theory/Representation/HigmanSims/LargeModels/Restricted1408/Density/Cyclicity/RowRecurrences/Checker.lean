module

public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Soundness of the packed recurrence checks

A step stores a proposed packed input, a generator choice and an output.
`products` checks its literal list product. Independently, `correspondence`
compares outputs and choices with the published lists, while `parentScan`
checks all input values in a single forward pass through the parent rows.
It consumes every child of a parent before moving to the next row; a check
can succeed only when every proposed input has been checked.

These soundness lemmas are instantiated by `Arithmetic.lean` on the unchanged
degree-1408 HS tables. Source and conventions: `../source/README.md`.
-/

@[expose] public section

namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences

structure Step where
  input : Nat
  choice : Bool
  output : Nat

def products (a b : List Nat) (ss : List Step) : Bool :=
  ss.all fun s => decide (PackedBinaryRows.listProduct s.input 0
    (if s.choice then b else a) = s.output)

theorem products_sound (a b : List Nat) (ss : List Step) (h : products a b ss = true)
    (s : Step) (hs : s ∈ ss) :
    PackedBinaryRows.listProduct s.input 0 (if s.choice then b else a) = s.output := by
  exact of_decide_eq_true (List.all_eq_true.mp h s hs)

theorem products_flatten (a b : List Nat) (blocks : List (List Step))
    (h : blocks.all (products a b) = true) : products a b blocks.flatten = true := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa only [List.flatten_cons, products, List.all_append, Bool.and_eq_true]
      using And.intro h.1 (ih h.2)

def inputs : List Step → List Nat → List (Nat × Nat)
  | s :: ss, p :: ps => (p, s.input) :: inputs ss ps
  | _, _ => []

def correspondence : List Step → List Nat → List Nat → List Bool → Bool
  | [], [], [], [] => true
  | s :: ss, y :: ys, _p :: ps, b :: bs =>
    (s.output == y) && (s.choice == b) && correspondence ss ys ps bs
  | _, _, _, _ => false

theorem correspondence_sound (ss : List Step) (ys ps : List Nat)
    (bs : List Bool) (h : correspondence ss ys ps bs = true)
    (i : Nat) (hi : i < ys.length) :
    ∃ s ∈ ss, (ps[i]!, s.input) ∈ inputs ss ps ∧ s.output = ys[i]! ∧ s.choice = bs[i]! := by
  induction ss generalizing ys ps bs i with
  | nil =>
    cases ys <;> cases ps <;> cases bs <;> simp_all [correspondence]
  | cons s ss ih =>
    cases ys with
    | nil => simp at hi
    | cons y ys =>
      cases ps with
      | nil => simp [correspondence] at h
      | cons p ps =>
        cases bs with
        | nil => simp [correspondence] at h
        | cons b bs =>
          simp only [correspondence, Bool.and_eq_true, beq_iff_eq] at h
          cases i with
          | zero =>
            exact ⟨s, List.mem_cons_self, List.mem_cons_self, h.1.1, h.1.2⟩
          | succ i =>
            obtain ⟨t, ht, hin, hout, hb⟩ := ih ys ps bs h.2 i (Nat.lt_of_succ_lt_succ hi)
            exact ⟨t, List.mem_cons_of_mem s ht, List.mem_cons_of_mem _ hin, hout, hb⟩

/-- Consume all proposed inputs at the current parent index. -/
def consume (start r : Nat) : List (Nat × Nat) → Option (List (Nat × Nat))
  | [] => some []
  | p :: ps =>
    if p.1 = start then
      if p.2 = r then consume start r ps else none
    else some (p :: ps)

theorem consume_sound (f : Nat → Nat) (start r : Nat) (hr : f start = r)
    (ps rest : List (Nat × Nat)) (h : consume start r ps = some rest)
    (hrest : ∀ p ∈ rest, f p.1 = p.2) : ∀ p ∈ ps, f p.1 = p.2 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [consume] at h
    split at h
    next hp =>
      split at h
      next hx =>
        have ht := ih h
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simpa only [hp, hx] using hr
        · exact ht q hq
      next hx => cases h
    next hp =>
      have he := Option.some.inj h
      simpa only [he] using hrest

/-- Scan the parent row list once; consume its children before moving forward. -/
def parentScan (start : Nat) : List Nat → List (Nat × Nat) → Bool
  | [], ps => ps.isEmpty
  | r :: rs, ps =>
    match consume start r ps with
    | none => false
    | some rest => parentScan (start + 1) rs rest

theorem parentScan_sound (f : Nat → Nat) (start : Nat) (rows : List Nat)
    (ps : List (Nat × Nat)) (h : parentScan start rows ps = true)
    (hrows : ∀ i, i < rows.length → f (start + i) = rows[i]!) :
    ∀ p ∈ ps, f p.1 = p.2 := by
  induction rows generalizing start ps with
  | nil =>
    have he : ps = [] := List.isEmpty_iff.mp h
    simp [he]
  | cons r rows ih =>
    cases hc : consume start r ps with
    | none => simp [parentScan, hc] at h
    | some rest =>
      have ht : parentScan (start + 1) rows rest = true := by
        simpa only [parentScan, hc] using h
      have hr : f start = r := by simpa using hrows 0 (by simp)
      apply consume_sound f start r hr ps rest hc
      apply ih (start + 1) rest ht
      intro i hi
      simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
        hrows (i + 1) (by simpa using hi)

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences
