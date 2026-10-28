module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.ReducedPresentation
public import Theory.GroupTheory.CosetWordCertificate.Schreier

/-!
# A 23-coset reduction of the reduced point presentation

A tree in the candidate 23-point action supplies 24 non-tree edges. The free
edge identities give an actual cover, and the 437 rewritten defining relations
hold by telescoping. A finite bound 443520 for this explicit presentation gives
the required bound 443520 for `ReducedPresented`. The action is used only to
propose the table; neither faithfulness nor its native group order is assumed.
Source: ATLAS M24G1-P1 via `PointSchreier`; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer
open Subgroup.CosetWordCertificate

def reducedGenerator (a : Fin 2) : ReducedPresented := PresentedGroup.of a

theorem reduced_generator_relations (r : Fin 19) :
    eval reducedGenerator (reducedRelatorLetters r) = 1 := by
  have hm : FreeGroup.lift reducedGenerator = PresentedGroup.mk (Set.range reducedRelator) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  change FreeGroup.lift reducedGenerator (reducedRelator r) = 1
  rw [hm]
  exact PresentedGroup.one_of_mem ⟨r, rfl⟩

def representativeWord : Fin 23 → Word (Fin 2) :=
  ![[],
    [(0, true)],
    [(0, false)],
    [(1, true)],
    [(1, false)],
    [(0, true), (1, true)],
    [(0, true), (1, false)],
    [(0, false), (1, true)],
    [(0, false), (1, false)],
    [(1, true), (0, true)],
    [(1, true), (0, false)],
    [(1, true), (1, true)],
    [(1, false), (1, false)],
    [(0, true), (1, true), (0, true)],
    [(0, false), (1, true), (0, false)],
    [(0, false), (1, true), (1, true)],
    [(1, true), (0, false), (1, false)],
    [(1, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true)],
    [(1, false), (1, false), (0, false)],
    [(0, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, false)],
    [(0, false), (1, true), (1, true), (1, true)]]

def destination (i : Fin 23) (a : Letter (Fin 2)) : Fin 23 :=
  if a.2 then (![![1,
    2,
    0,
    9,
    4,
    13,
    6,
    8,
    14,
    10,
    3,
    5,
    18,
    11,
    7,
    15,
    16,
    21,
    19,
    12,
    20,
    22,
    17],
    ![3,
    5,
    7,
    11,
    0,
    9,
    1,
    15,
    2,
    8,
    6,
    17,
    4,
    20,
    12,
    22,
    10,
    16,
    14,
    21,
    18,
    13,
    19]] : Fin 2 → Fin 23 → Fin 23) a.1 i
  else (![![2,
    0,
    1,
    10,
    4,
    11,
    6,
    14,
    7,
    3,
    9,
    13,
    19,
    5,
    8,
    15,
    16,
    22,
    12,
    18,
    20,
    17,
    21],
    ![4,
    6,
    8,
    0,
    12,
    1,
    10,
    2,
    9,
    5,
    16,
    3,
    14,
    21,
    18,
    7,
    17,
    11,
    20,
    22,
    13,
    19,
    15]] : Fin 2 → Fin 23 → Fin 23) a.1 i

def symbolWord : Fin 24 → Word (Fin 2) :=
  ![[(0, true), (0, true), (0, true)],
    [(1, false), (0, true), (1, true)],
    [(0, true), (1, true), (1, true), (0, false), (1, false)],
    [(0, true), (1, false), (0, true), (1, true), (0, false)],
    [(0, false), (1, true), (0, true), (1, true), (0, true)],
    [(0, false), (1, false), (0, true), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (0, true), (0, true), (1, false)],
    [(1, true), (0, true), (1, true), (1, true), (0, true)],
    [(1, true), (0, false), (1, true), (1, true), (0, false)],
    [(1, true), (1, true), (0, true), (1, false), (0, false)],
    [(0, true), (1, true), (0, true), (0, true), (1, false), (1, false)],
    [(0, false), (1, true), (0, false), (1, true), (1, true), (1, true)],
    [(0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true)],
    [(1, true), (0, false), (1, false), (0, true), (1, true), (0, true), (1, false)],
    [(1, true), (1, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false)],
    [(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, false)],
    [(1, false), (1, false), (0, true), (0, true), (0, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true)],
    [(1, false), (1, false), (0, false), (1, true), (1, true), (0, false), (1, false), (0, false)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, false), (1, false), (0, false)],
    [(0, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (1, false), (0, true)],
    [(0, false), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false)],
    [(0, false), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true)]]

def positiveWord (i : Fin 23) (a : Fin 2) : Word (Fin 24) :=
  (![![[],
    []],
    ![[(0, true)],
    []],
    ![[],
    []],
    ![[],
    []],
    ![[(1, true)],
    []],
    ![[],
    [(2, true)]],
    ![[(3, true)],
    []],
    ![[(4, true)],
    []],
    ![[(5, true)],
    []],
    ![[(6, true)],
    [(7, true)]],
    ![[],
    [(8, true)]],
    ![[(9, true)],
    []],
    ![[],
    []],
    ![[(10, true)],
    []],
    ![[],
    [(11, true)]],
    ![[(12, true)],
    []],
    ![[(13, true)],
    []],
    ![[(14, true)],
    [(15, true)]],
    ![[(16, true)],
    [(17, true)]],
    ![[],
    [(18, true)]],
    ![[(19, true)],
    [(20, true)]],
    ![[(21, true)],
    []],
    ![[(22, true)],
    [(23, true)]]] : Fin 23 → Fin 2 → Word (Fin 24)) i a

def edgeWord (i : Fin 23) (a : Letter (Fin 2)) : Word (Fin 24) :=
  if a.2 then positiveWord i a.1
  else FreeGroup.invRev (positiveWord (destination i a) a.1)

def representative (i : Fin 23) : ReducedPresented := eval reducedGenerator (representativeWord i)
def symbol (s : Fin 24) : ReducedPresented := eval reducedGenerator (symbolWord s)

def expand : Word (Fin 24) → Word (Fin 2)
  | [] => []
  | (s, b) :: w => (if b then symbolWord s else FreeGroup.invRev (symbolWord s)) ++ expand w

private theorem eval_expand (w : Word (Fin 24)) :
    eval reducedGenerator (expand w) = eval symbol w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨a, b⟩
    cases b <;> simp [expand, eval_append, eval_invRev, eval_cons, ih, symbol]

private theorem positiveCheck : ∀ (i : Fin 23) (a : Fin 2),
    reduce (expand (positiveWord i a)) =
      reduce (representativeWord i ++ [(a, true)] ++
        FreeGroup.invRev (representativeWord (destination i (a, true)))) := by
  decide +kernel

theorem positiveWord_eval (i : Fin 23) (a : Fin 2) :
    eval symbol (positiveWord i a) =
      representative i * reducedGenerator a * (representative (destination i (a, true)))⁻¹ := by
  rw [← eval_expand, ← eval_reduce, positiveCheck, eval_reduce]
  simp only [eval_append, eval_invRev, eval_letter, ↓reduceIte, representative]

private theorem destination_reverse : ∀ (i : Fin 23) (a : Fin 2),
    destination (destination i (a, false)) (a, true) = i := by
  decide +kernel

theorem edgeWord_eval (i : Fin 23) (a : Letter (Fin 2)) :
    eval symbol (edgeWord i a) =
      representative i * eval reducedGenerator [a] * (representative (destination i a))⁻¹ := by
  rcases a with ⟨a, b⟩
  cases b
  · simp only [edgeWord, Bool.false_eq_true, ↓reduceIte, eval_invRev, positiveWord_eval,
      destination_reverse, eval_letter, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  · simpa only [edgeWord, ↓reduceIte, eval_letter] using positiveWord_eval i a

def endpoint (i : Fin 23) : Word (Fin 2) → Fin 23
  | [] => i
  | a :: w => endpoint (destination i a) w

def traceWord (i : Fin 23) : Word (Fin 2) → Word (Fin 24)
  | [] => []
  | a :: w => edgeWord i a ++ traceWord (destination i a) w

theorem traceWord_eval (i : Fin 23) (w : Word (Fin 2)) :
    eval symbol (traceWord i w) =
      representative i * eval reducedGenerator w * (representative (endpoint i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [traceWord, endpoint]
  | cons a w ih =>
    rw [traceWord, eval_append, edgeWord_eval, ih, endpoint,
      show eval reducedGenerator (a :: w) = eval reducedGenerator [a] * eval reducedGenerator w from
        eval_append reducedGenerator [a] w]
    simp [mul_assoc]

private theorem sourceLoop : ∀ (i : Fin 23) (r : Fin 19), endpoint i (reducedRelatorLetters r) = i := by
  decide +kernel

/-- All original relators at every vertex, with literal tree-based rewriting. -/
def relatorLetters (r : Fin 23 × Fin 19) : Word (Fin 24) := traceWord r.1 (reducedRelatorLetters r.2)

theorem relatorLetters_eval (r : Fin 23 × Fin 19) : eval symbol (relatorLetters r) = 1 := by
  rw [relatorLetters, traceWord_eval, reduced_generator_relations, sourceLoop]
  simp

def relator (r : Fin 23 × Fin 19) : FreeGroup (Fin 24) := FreeGroup.mk (relatorLetters r)
abbrev Presented := PresentedGroup (Set.range relator)
def subgroup : Subgroup ReducedPresented := Subgroup.closure (Set.range symbol)

def toReduced : Presented →* ReducedPresented :=
  PresentedGroup.toGroup (f := symbol) (by
    rintro _ ⟨r, rfl⟩
    exact relatorLetters_eval r)

@[simp] theorem toReduced_generator (s : Fin 24) :
    toReduced (PresentedGroup.of s) = symbol s := PresentedGroup.toGroup.of _

theorem toReduced_range : toReduced.range = subgroup := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (Set.range relator),
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext s
  exact toReduced_generator s

/-- A genuine abstract cover: every transition multiplier is a word in the
specified Schreier generators. -/
def cover : Subgroup.GeneratorCosetCover subgroup reducedGenerator (Fin 23) where
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
theorem reduced_bound_of_stabilizer_bound
    (h : Finite Presented ∧ Nat.card Presented ≤ 443520) :
    Finite ReducedPresented ∧ Nat.card ReducedPresented ≤ 10200960 := by
  let : Finite Presented := h.1
  have hf : Finite toReduced.range := Finite.of_surjective _ toReduced.rangeRestrict_surjective
  have hc : Nat.card toReduced.range ≤ Nat.card Presented :=
    Nat.card_le_card_of_surjective _ toReduced.rangeRestrict_surjective
  rw [toReduced_range] at hf hc
  let : Finite subgroup := hf
  obtain ⟨hf', hc'⟩ := cover.finite_card_le (PresentedGroup.closure_range_of (Set.range reducedRelator))
  refine ⟨hf', hc'.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 23 (hc.trans h.2)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer
