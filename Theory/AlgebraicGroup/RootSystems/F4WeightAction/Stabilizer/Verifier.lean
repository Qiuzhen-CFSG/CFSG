module
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Certificate

/-! Boolean integer checkers with structural soundness proofs. Keeping proof
construction outside the table reduction makes the finite census inexpensive
and leaves every arithmetic claim checked by the Lean kernel. -/
@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer.Verifier
open Data

def row (a : Fin 24) (b : Fin 48) : Fin 1152 := ⟨a.val*48+b.val, by omega⟩
def vectorOK (a b : V) : Bool := (List.finRange 4).all fun i => a i == b i
def matrixOK (a b : M) : Bool :=
  (List.finRange 4).all fun i => (List.finRange 4).all fun j => a i j == b i j

theorem vectorOK_sound {a b : V} (h : vectorOK a b = true) : a = b := by
  simp only [vectorOK, List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq] at h
  exact funext h

theorem matrixOK_sound {a b : M} (h : matrixOK a b = true) : a = b := by
  simp only [matrixOK, List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq] at h
  exact funext fun i => funext (h i)

def nextOK (k : Fin 1152) : Bool :=
  (List.finRange 4).all fun i => (List.finRange 4).all fun j =>
    (List.finRange 4).all fun x =>
      (matrix k x j - matrix k i j * cartan i x == matrix (next k i) x j)

theorem nextOK_sound {k : Fin 1152} (h : nextOK k = true) (i j : Fin 4) :
    reflection i (fun a => matrix k a j) = fun a => matrix (next k i) a j := by
  simp only [nextOK, List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq] at h
  ext x
  exact h i j x

def parentOK (k : Fin 1152) : Bool := if k = 0 then true else
  decide ((parent k).val < k.val ∧ words k = step k :: words (parent k) ∧
    next (parent k) (step k) = k)

theorem parentOK_sound {k : Fin 1152} (h : parentOK k = true) (hk : k ≠ 0) :
    (parent k).val < k.val ∧ words k = step k :: words (parent k) ∧
      next (parent k) (step k) = k := by
  simpa only [parentOK, if_neg hk, decide_eq_true_eq] using h

def pathOK : Fin 1152 → List (Fin 24 × Fin 1152 × V) → Bool
 | k, [] => k == 0
 | k, x::xs => matrixOK (matrix k) (matrix (refIndex x.1) * matrix x.2.1) && pathOK x.2.1 xs

theorem pathOK_sound {k l} (h : pathOK k l = true) : pathValid k l := by
  induction l generalizing k with
  | nil => exact beq_iff_eq.mp h
  | cons x xs ih =>
    obtain ⟨h1,h2⟩ := (Bool.and_eq_true _ _).mp h
    exact ⟨matrixOK_sound h1, ih h2⟩

def branchOK (k : Fin 1152) : Bool := match kind k with
 | none => pathOK k (path k)
 | some j => exceptionIndex j == k

def witnessOK (k : Fin 1152) : Bool := (path k).all fun x =>
  vectorOK ((matrix k).mulVec x.2.2 - x.2.2) ((2:ℤ) • weights x.1)

def rowOK (a : Fin 24) : Bool := (List.finRange 48).all fun b =>
  parentOK (row a b) && nextOK (row a b) && branchOK (row a b) && witnessOK (row a b)

theorem rowOK_sound {a : Fin 24} (h : rowOK a = true) (b : Fin 48) :
    parentOK (row a b) = true ∧ nextOK (row a b) = true ∧
    branchOK (row a b) = true ∧ witnessOK (row a b) = true := by
  simp only [rowOK, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.and_eq_true] at h
  exact ⟨(h b).1.1.1, (h b).1.1.2, (h b).1.2, (h b).2⟩

theorem rows_sound (h : ∀ a, rowOK a = true) (k : Fin 1152) :
    parentOK k = true ∧ nextOK k = true ∧ branchOK k = true ∧ witnessOK k = true := by
  let a : Fin 24 := ⟨k.val / 48, by omega⟩
  let b : Fin 48 := ⟨k.val % 48, by omega⟩
  have hk : row a b = k := by apply Fin.ext; dsimp [row, a, b]; omega
  simpa only [hk] using rowOK_sound (h a) b

end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer.Verifier
