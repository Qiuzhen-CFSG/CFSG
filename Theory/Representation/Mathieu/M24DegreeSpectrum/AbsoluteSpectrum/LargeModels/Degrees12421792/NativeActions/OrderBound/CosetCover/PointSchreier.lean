module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalPresentation
public import Theory.GroupTheory.CosetWordCertificate.Schreier

/-!
# A 24-coset Schreier reduction of the literal M24 presentation

The right-action table is the inverse of the two native degree-24 permutations.
A breadth-first tree at point 0 supplies 25 non-tree positive edges. Their
actual group elements satisfy the 168 rewritten source relators by telescoping.
They generate a subgroup with an actual 24-coset cover of `UniversalGroup`.
Consequently an upper bound of 10200960 for this independent Schreier
presentation would imply the desired ambient upper bound 244823040.

Only the table, tree, and free-word identities are finite checks. No permutation
image is assumed faithful and no abstract finite bound is asserted.
Source: John Bray, ATLAS M24G1-P1; see `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier
open Subgroup.CosetWordCertificate

def representativeWord : Fin 24 → Word (Fin 2) :=
  ![[],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true)],
    [(1, true), (0, true), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)],
    [(1, true), (0, true)],
    [(1, true), (0, true), (1, true), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true)],
    [(1, true), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, false)],
    [(1, true), (0, true), (1, true)],
    [(1, true)],
    [(0, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)],
    [(1, false), (0, true)],
    [(1, false)]]

def destination (i : Fin 24) (a : Letter (Fin 2)) : Fin 24 :=
  if a.2 then (![![20,
    4,
    7,
    17,
    1,
    13,
    9,
    2,
    15,
    6,
    19,
    18,
    21,
    5,
    16,
    8,
    14,
    3,
    11,
    10,
    0,
    12,
    23,
    22],
    ![19,
    6,
    14,
    15,
    1,
    10,
    4,
    7,
    8,
    3,
    18,
    11,
    12,
    16,
    21,
    9,
    17,
    13,
    5,
    23,
    20,
    2,
    22,
    0]] : Fin 2 → Fin 24 → Fin 24) a.1 i
  else (![![20,
    4,
    7,
    17,
    1,
    13,
    9,
    2,
    15,
    6,
    19,
    18,
    21,
    5,
    16,
    8,
    14,
    3,
    11,
    10,
    0,
    12,
    23,
    22],
    ![23,
    4,
    21,
    9,
    6,
    18,
    1,
    7,
    8,
    15,
    5,
    11,
    12,
    17,
    2,
    3,
    13,
    16,
    10,
    0,
    20,
    14,
    22,
    19]] : Fin 2 → Fin 24 → Fin 24) a.1 i

def symbolWord : Fin 25 → Word (Fin 2) :=
  ![[(0, true), (0, true)],
    [(0, true), (1, true), (0, false)],
    [(1, true), (1, true), (1, true)],
    [(1, true), (0, true), (0, true), (1, false)],
    [(1, false), (0, true), (0, true), (1, true)],
    [(1, false), (0, true), (1, true), (0, false), (1, true)],
    [(1, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, true), (0, true), (0, true), (1, false), (0, false), (1, false)],
    [(1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (0, true), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (0, true), (1, false), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (0, true), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)]]

def positiveWord (i : Fin 24) (a : Fin 2) : Word (Fin 25) :=
  (![![[],
    []],
    ![[(24, true)],
    []],
    ![[],
    []],
    ![[(12, true)],
    []],
    ![[(22, true)],
    [(23, true)]],
    ![[],
    []],
    ![[(21, true)],
    []],
    ![[(17, true)],
    [(18, true)]],
    ![[(19, true)],
    [(20, true)]],
    ![[],
    []],
    ![[(3, true)],
    []],
    ![[(7, true)],
    [(8, true)]],
    ![[(15, true)],
    [(16, true)]],
    ![[(9, true)],
    []],
    ![[(11, true)],
    []],
    ![[],
    [(14, true)]],
    ![[],
    [(10, true)]],
    ![[],
    []],
    ![[],
    [(6, true)]],
    ![[],
    [(2, true)]],
    ![[(0, true)],
    [(1, true)]],
    ![[],
    [(13, true)]],
    ![[(4, true)],
    [(5, true)]],
    ![[],
    []]] : Fin 24 → Fin 2 → Word (Fin 25)) i a

def edgeWord (i : Fin 24) (a : Letter (Fin 2)) : Word (Fin 25) :=
  if a.2 then positiveWord i a.1
  else FreeGroup.invRev (positiveWord (destination i a) a.1)

def representative (i : Fin 24) : UniversalGroup := eval generator (representativeWord i)
def symbol (s : Fin 25) : UniversalGroup := eval generator (symbolWord s)

def expand : Word (Fin 25) → Word (Fin 2)
  | [] => []
  | (s, b) :: w => (if b then symbolWord s else FreeGroup.invRev (symbolWord s)) ++ expand w

private theorem eval_expand (w : Word (Fin 25)) :
    eval generator (expand w) = eval symbol w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨a, b⟩
    cases b <;> simp [expand, eval_append, eval_invRev, eval_cons, ih, symbol]

private theorem positiveCheck : ∀ (i : Fin 24) (a : Fin 2),
    reduce (expand (positiveWord i a)) =
      reduce (representativeWord i ++ [(a, true)] ++
        FreeGroup.invRev (representativeWord (destination i (a, true)))) := by
  decide +kernel

theorem positiveWord_eval (i : Fin 24) (a : Fin 2) :
    eval symbol (positiveWord i a) =
      representative i * generator a * (representative (destination i (a, true)))⁻¹ := by
  rw [← eval_expand, ← eval_reduce, positiveCheck, eval_reduce]
  simp only [eval_append, eval_invRev, eval_letter, ↓reduceIte, representative]

private theorem destination_reverse : ∀ (i : Fin 24) (a : Fin 2),
    destination (destination i (a, false)) (a, true) = i := by
  decide +kernel

theorem edgeWord_eval (i : Fin 24) (a : Letter (Fin 2)) :
    eval symbol (edgeWord i a) =
      representative i * eval generator [a] * (representative (destination i a))⁻¹ := by
  rcases a with ⟨a, b⟩
  cases b
  · simp only [edgeWord, Bool.false_eq_true, ↓reduceIte, eval_invRev, positiveWord_eval,
      destination_reverse, eval_letter, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  · simpa only [edgeWord, ↓reduceIte, eval_letter] using positiveWord_eval i a

def endpoint (i : Fin 24) : Word (Fin 2) → Fin 24
  | [] => i
  | a :: w => endpoint (destination i a) w

def traceWord (i : Fin 24) : Word (Fin 2) → Word (Fin 25)
  | [] => []
  | a :: w => edgeWord i a ++ traceWord (destination i a) w

theorem traceWord_eval (i : Fin 24) (w : Word (Fin 2)) :
    eval symbol (traceWord i w) =
      representative i * eval generator w * (representative (endpoint i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [traceWord, endpoint]
  | cons a w ih =>
    rw [traceWord, eval_append, edgeWord_eval, ih, endpoint,
      show eval generator (a :: w) = eval generator [a] * eval generator w from
        eval_append generator [a] w]
    simp [mul_assoc]

private theorem sourceLoop : ∀ (i : Fin 24) (r : Fin 7), endpoint i (sourceLetters r) = i := by
  decide +kernel

/-- All original relators at every vertex, with literal tree-based rewriting. -/
def relatorLetters (r : Fin 24 × Fin 7) : Word (Fin 25) := traceWord r.1 (sourceLetters r.2)

theorem relatorLetters_eval (r : Fin 24 × Fin 7) : eval symbol (relatorLetters r) = 1 := by
  rw [relatorLetters, traceWord_eval, sourceLetters_eq_one, sourceLoop]
  simp

def relator (r : Fin 24 × Fin 7) : FreeGroup (Fin 25) := FreeGroup.mk (relatorLetters r)
abbrev Presented := PresentedGroup (Set.range relator)
def subgroup : Subgroup UniversalGroup := Subgroup.closure (Set.range symbol)

def toUniversal : Presented →* UniversalGroup :=
  PresentedGroup.toGroup (f := symbol) (by
    rintro _ ⟨r, rfl⟩
    exact relatorLetters_eval r)

@[simp] theorem toUniversal_generator (s : Fin 25) :
    toUniversal (PresentedGroup.of s) = symbol s := PresentedGroup.toGroup.of _

theorem toUniversal_range : toUniversal.range = subgroup := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (Set.range relator),
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext s
  exact toUniversal_generator s

/-- A genuine abstract cover: every transition multiplier is a word in the
specified Schreier generators. -/
def cover : Subgroup.GeneratorCosetCover subgroup generator (Fin 24) where
  repr := representative
  initial := 0
  initial_eq := rfl
  step i a := by
    let h : subgroup := ⟨eval symbol (edgeWord i (a, true)),
      eval_mem_of_generators_mem subgroup symbol
        (fun s => Subgroup.subset_closure (Set.mem_range_self s)) _⟩
    refine ⟨h, destination i (a, true), ?_⟩
    change _ = eval symbol (edgeWord i (a, true)) * _
    rw [edgeWord_eval]
    simp only [eval_letter, ↓reduceIte, inv_mul_cancel_right]
  inv_step i a := by
    let h : subgroup := ⟨eval symbol (edgeWord i (a, false)),
      eval_mem_of_generators_mem subgroup symbol
        (fun s => Subgroup.subset_closure (Set.mem_range_self s)) _⟩
    refine ⟨h, destination i (a, false), ?_⟩
    change _ = eval symbol (edgeWord i (a, false)) * _
    rw [edgeWord_eval]
    simp only [eval_letter, Bool.false_eq_true, ↓reduceIte, inv_mul_cancel_right]

/-- The remaining order problem is explicit; this theorem does not assume or
assert faithfulness of the degree-24 permutation image. -/
theorem ambient_bound_of_presented_bound
    (h : Finite Presented ∧ Nat.card Presented ≤ 10200960) :
    Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040 := by
  let : Finite Presented := h.1
  have hf : Finite toUniversal.range := Finite.of_surjective _ toUniversal.rangeRestrict_surjective
  have hc : Nat.card toUniversal.range ≤ Nat.card Presented :=
    Nat.card_le_card_of_surjective _ toUniversal.rangeRestrict_surjective
  rw [toUniversal_range] at hf hc
  let : Finite subgroup := hf
  obtain ⟨hf', hc'⟩ := cover.finite_card_le (PresentedGroup.closure_range_of relators)
  refine ⟨hf', hc'.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 24 (hc.trans h.2)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier
