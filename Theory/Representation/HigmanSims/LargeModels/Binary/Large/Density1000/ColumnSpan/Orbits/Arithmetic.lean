module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Trees
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Arithmetic

/-!
# Plain-tree evaluation of the column-orbit certificate

The nongeneric row tree reuses the proved XOR append evaluator. Its products
and bit comparisons agree with the shared checked table views, so bounded
numerical checks feed the existing literal transpose and word-induction proofs.
Source: ATLAS HSG1-f2r1000B0 and `Binary/source/density1000.json`;
see `Orbits/source/README.md` for attribution and measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits
open RowArithmetic
open RowSpan (Tree)

def columnMatch (power x : Nat) : Tree → Bool
  | .leaf rs => listMatch power x rs
  | .node n l r => columnMatch power x l && columnMatch power (x >>> n) r

theorem columnMatch_eq (t : Tree) (ht : t.valid = true) (p x : Nat) :
    columnMatch p x t = listMatch p x t.rows := by
  induction t generalizing x with
  | leaf rs => rfl
  | node n l r il ir =>
    simp only [Tree.valid, Bool.and_eq_true, decide_eq_true_eq] at ht
    simp only [columnMatch, Tree.rows, listMatch_append]
    rw [il ht.1.2, ir ht.2, ht.1.1]

theorem product_eq (t : Tree) (s : RowTree) (ht : t.valid = true)
    (hs : s.valid = true) (hrows : t.rows = s.rows) (x : Nat) :
    t.product x = s.product x := by
  rw [t.product_eq ht, s.product_eq hs, hrows]

theorem columnMatch_shared (t : Tree) (s : RowTree) (ht : t.valid = true)
    (hs : s.valid = true) (hrows : t.rows = s.rows) (p x : Nat) :
    columnMatch p x t = s.columnMatch p x := by
  rw [columnMatch_eq t ht, s.columnMatch_eq hs, hrows]

/-- Explicit intermediate masks keep the kernel checks local to small leaves. -/
theorem columnMatch_node (p x y n : Nat) (l r : Tree)
    (hs : x / 2 ^ n = y)
    (hl : columnMatch p x l = true) (hr : columnMatch p y r = true) :
    columnMatch p x (.node n l r) = true := by
  simp only [columnMatch, Bool.and_eq_true, Nat.shiftRight_eq_div_pow, hs]
  exact ⟨hl, hr⟩

theorem transpose_one (t : Tree) (target source : RowTree)
    (ht : t.valid = true) (hu : target.valid = true) (hr : t.rows = target.rows)
    (i p x : Nat) (hp : p = 2 ^ i) (hx : source.get i = x)
    (h : columnMatch p x t = true) : target.columnMatch (2 ^ i) (source.get i) = true := by
  rw [hx, ← hp, ← columnMatch_shared t target ht hu hr]
  exact h

theorem on_single {P : Nat → Prop} (i : Nat) (h : P i) : On P i (i+1) := by
  intro j hlo hhi
  have : j = i := by omega
  subst j
  exact h

def fastOrbitCase (a b : Tree) (cols : RowTree) (words : Table (List Bool))
    (i : Nat) (s : Step) : Bool :=
  decide (cols.get s.parent = s.input) && decide (cols.get i = s.output) &&
  decide (s.parent < i) && decide (words.get i = s.letter :: words.get s.parent) &&
  decide ((if s.letter then b else a).product s.input = s.output)

theorem orbitOn (a b : Tree) (targetA targetB cols : RowTree) (words : Table (List Bool))
    (ha : a.valid = true) (hb : b.valid = true)
    (hat : targetA.valid = true) (hbt : targetB.valid = true)
    (hra : a.rows = targetA.rows) (hrb : b.rows = targetB.rows)
    (lo : Nat) (xs : List Step)
    (h : caseChecks (fastOrbitCase a b cols words) lo xs = true) :
    On (OrbitStep targetA targetB cols words) lo (lo+xs.length) := by
  intro i hlo hhi
  obtain ⟨s, hs⟩ := on_of_caseChecks _ _ _ h i hlo hhi
  simp only [fastOrbitCase, Bool.and_eq_true, decide_eq_true_eq] at hs
  rcases hs with ⟨⟨⟨⟨hx, hy⟩, hlt⟩, hw⟩, hv⟩
  refine ⟨s.parent, s.letter, hlt, hw, ?_⟩
  rw [hx, hy]
  cases hc : s.letter with
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hv
    exact (product_eq a targetA ha hat hra s.input).symm.trans hv
  | true =>
    simp only [hc, ↓reduceIte] at hv
    exact (product_eq b targetB hb hbt hrb s.input).symm.trans hv

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits
