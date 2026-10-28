module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate.ScalarData

/-!
# Soundness of the finite pair-tree checks

A balanced Boolean range check certifies the scalar action table. Each tree
transition first checks its scalar index and recovers its exact input mask,
then uses the certified image. A second recovery map for packed mask pairs
proves injectivity. The final constructor checks the literal root and packages
all the bounds and edges into the unchanged `OrbitCertificate` contract.

Source: retained ATLAS J4G1-max2W1 and kernel_candidate.json, as documented in
Centralizer/source. The scalar and tree checks are discharged in `Checks`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree

def allBlock (p : Nat → Bool) : Nat → Nat → Bool
  | 0, start => p start
  | depth + 1, start => allBlock p depth start && allBlock p depth (start + 2 ^ depth)

theorem allBlock_spec (p : Nat → Bool) (depth start : Nat)
    (h : allBlock p depth start = true) :
    ∀ n, start ≤ n → n < start + 2 ^ depth → p n = true := by
  induction depth generalizing start with
  | zero =>
    intro n hlo hhi
    have hn : n = start := by omega
    subst n
    exact h
  | succ depth ih =>
    simp only [allBlock, Bool.and_eq_true] at h
    intro n hlo hhi
    rw [Nat.pow_succ, Nat.mul_two] at hhi
    by_cases hn : n < start + 2 ^ depth
    · exact ih start h.1 n hlo hn
    · exact ih (start + 2 ^ depth) h.2 n (by omega) (by omega)


def scalarMask (i : Nat) : Nat := scalarRow i % 8192

def scalarImage (s : Bool) (i : Nat) : Nat :=
  (scalarRow i >>> (if s then 26 else 13)) % 8192

def scalarCheck (i : Nat) : Bool :=
  if i < 1386 then
    (fastAction false (scalarMask i) == scalarImage false i) &&
    (fastAction true (scalarMask i) == scalarImage true i)
  else true

theorem scalarCheck_spec (i : Nat) (hi : i < 1386)
    (h : scalarCheck i = true) (s : Bool) :
    maskAction s (scalarMask i) = scalarImage s i := by
  have h' : maskAction false (scalarMask i) = scalarImage false i ∧
      maskAction true (scalarMask i) = scalarImage true i := by
    simpa only [scalarCheck, if_pos hi, Bool.and_eq_true, beq_iff_eq, action_fast] using h
  cases s
  · exact h'.1
  · exact h'.2

def stepCheck (s : Bool) (m n : Nat) : Bool :=
  decide (scalarIndex m < 1386) &&
    ((scalarMask (scalarIndex m) == m) && (scalarImage s (scalarIndex m) == n))

theorem stepCheck_spec
    (actions : ∀ i, i < 1386 → scalarCheck i = true)
    (s : Bool) (m n : Nat) (h : stepCheck s m n = true) : maskAction s m = n := by
  have h' : scalarIndex m < 1386 ∧ scalarMask (scalarIndex m) = m ∧
      scalarImage s (scalarIndex m) = n := by
    simpa only [stepCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h
  have he := scalarCheck_spec (scalarIndex m) h'.1 (actions _ h'.1) s
  rw [h'.2.1, h'.2.2] at he
  exact he
def rowU (i : Nat) : Nat := packedRow i % 8192

def rowV (i : Nat) : Nat := (packedRow i >>> 13) % 8192

def rowParent (i : Nat) : Nat := (packedRow i >>> 26) % 8192

def rowUseY (i : Nat) : Bool := (packedRow i).testBit 39


def rowCheck (i : Nat) : Bool :=
  decide (rowParent i < 5544) &&
    ((recover (8192 * rowU i + rowV i) == i) &&
      ((i == 0) || (decide (rowParent i < i) &&
        (stepCheck (rowUseY i) (rowU (rowParent i)) (rowU i) &&
         stepCheck (rowUseY i) (rowV (rowParent i)) (rowV i)))))

theorem rowCheck_spec (actions : ∀ i, i < 1386 → scalarCheck i = true)
    (i : Nat) (h : rowCheck i = true) :
    rowParent i < 5544 ∧ recover (8192 * rowU i + rowV i) = i ∧
      (i = 0 ∨ (rowParent i < i ∧
        maskAction (rowUseY i) (rowU (rowParent i)) = rowU i ∧
        maskAction (rowUseY i) (rowV (rowParent i)) = rowV i)) := by
  have h' : rowParent i < 5544 ∧ recover (8192 * rowU i + rowV i) = i ∧
      (i = 0 ∨ (rowParent i < i ∧
        stepCheck (rowUseY i) (rowU (rowParent i)) (rowU i) = true ∧
        stepCheck (rowUseY i) (rowV (rowParent i)) (rowV i) = true)) := by
    simpa only [rowCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] using h
  refine ⟨h'.1, h'.2.1, h'.2.2.imp id ?_⟩
  rintro ⟨hp, hu, hv⟩
  exact ⟨hp, stepCheck_spec actions _ _ _ hu, stepCheck_spec actions _ _ _ hv⟩
theorem certificate_of_checks
    (actions : ∀ i, i < 1386 → scalarCheck i = true)
    (checked : ∀ i, i < 5544 → rowCheck i = true) : Nonempty OrbitCertificate := by
  have facts := fun i hi => rowCheck_spec actions i (checked i hi)
  let masks (i : Fin 5544) : Fin 8192 × Fin 8192 :=
    (⟨rowU i.val, Nat.mod_lt _ (by decide)⟩,
     ⟨rowV i.val, Nat.mod_lt _ (by decide)⟩)
  let parent (i : Fin 5544) : Fin 5544 :=
    ⟨rowParent i.val, (facts i.val i.isLt).1⟩
  refine ⟨{
    masks := masks
    parent := parent
    useY := fun i => rowUseY i.val
    root := ?_
    decrease := ?_
    edge := ?_
    injective := ?_ }⟩
  · rfl
  · intro i hi
    have hz : i.val ≠ 0 := fun hz => hi (Fin.ext hz)
    exact ((facts i.val i.isLt).2.2.resolve_left hz).1
  · intro i hi
    have hz : i.val ≠ 0 := fun hz => hi (Fin.ext hz)
    have he := ((facts i.val i.isLt).2.2.resolve_left hz).2
    exact Prod.ext he.1 he.2
  · intro i j hij
    apply Fin.ext
    have hu : rowU i.val = rowU j.val := congrArg (fun p => p.1.val) hij
    have hv : rowV i.val = rowV j.val := congrArg (fun p => p.2.val) hij
    calc
      i.val = recover (8192 * rowU i.val + rowV i.val) := (facts i.val i.isLt).2.1.symm
      _ = recover (8192 * rowU j.val + rowV j.val) := by rw [hu, hv]
      _ = j.val := (facts j.val j.isLt).2.1

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
