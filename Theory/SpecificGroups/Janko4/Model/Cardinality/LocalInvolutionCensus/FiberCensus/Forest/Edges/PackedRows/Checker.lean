module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Literals
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Nodes

/-!
# A proved arithmetic checker for the crossing rows

A natural-number scan computes the same XOR as `packedRow`. Certified entry
lookups avoid reduction through `Vector.ofFn`; the kernel fold retains exactly
the thirteen increasing-bit factors. `check_iff` and `fastTuple_eq` identify
this arithmetic with the existing public `PackedEdge` equation.

Source: the unchanged ATLAS J4G1-max2W1 data; see `Edges/source/README.md`
and `PackedRows/source/README.md`. No actor evaluation is assumed here.
-/

@[expose] public section

namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation Janko4.GeneratorCertificates

noncomputable def scanRow (x : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | count + 1, offset =>
    (if x.testBit offset then f offset else 0) ^^^ scanRow x f count (offset + 1)

theorem scanRow_eq (x : ℕ) (f : ℕ → ℕ) (count offset : ℕ) :
    scanRow x f count offset = xorList (List.ofFn (fun i : Fin count =>
      if x.testBit (offset + i.val) then f (offset + i.val) else 0)) := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [scanRow, List.ofFn_succ, xorList, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ,
      Nat.add_left_comm, Nat.add_comm]
    rfl

noncomputable def rowAction (x : ℕ) (f : Fin 112 → ℕ) : ℕ :=
  scanRow x (fun i => f (Fin.ofNat 112 i)) 112 0

theorem rowAction_eq (x : ℕ) (f : Fin 112 → ℕ) :
    rowAction x f = xorList (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  simp only [rowAction, scanRow_eq, Nat.zero_add, Fin.ofNat_val_eq_self]

theorem literalEntry_get (m : Fin 17) :
    (fun i : Fin 112 => literalEntry m i.val) = (literalRows m).get :=
  funext (literalEntry_eq m)

noncomputable def liftEntry (j : Fin 4) : Fin 112 → ℕ :=
  ![fun i => 2^i.val, fun i => literalEntry 0 i.val,
    fun i => literalEntry 2 i.val, fun i => literalEntry 3 i.val] j

theorem liftEntry_eq (j : Fin 4) : liftEntry j = (liftRows j).get := by
  fin_cases j <;> funext i <;>
    simp [liftEntry, liftRows, literalEntry_eq, literalRows, packedOne, get_ofFn]

noncomputable def wordEntries : Fin 4 → List (Fin 112 → ℕ) :=
  ![[],
    [fun i => literalEntry 4 i.val, fun i => literalEntry 5 i.val,
      fun i => literalEntry 6 i.val, fun i => literalEntry 7 i.val],
    [fun i => literalEntry 8 i.val, fun i => literalEntry 9 i.val,
      fun i => literalEntry 10 i.val, fun i => literalEntry 11 i.val],
    [fun i => literalEntry 12 i.val, fun i => literalEntry 13 i.val,
      fun i => literalEntry 14 i.val, fun i => literalEntry 15 i.val,
      fun i => literalEntry 16 i.val]]

theorem wordEntries_eq (j : Fin 4) : wordEntries j = (wordRows j).map Vector.get := by
  fin_cases j <;> simp [wordEntries, wordRows, literalEntry_get, literalRows]

noncomputable def actorEntries (j : Fin 4) : List (Fin 112 → ℕ) :=
  if j = 0 then [fun i => literalEntry 0 i.val, fun i => literalEntry 1 i.val]
  else List.ofFn (fun n : Fin 13 => fun i : Fin 112 => entry n.val i.val) ++ wordEntries j

theorem actorEntries_eq (j : Fin 4) : actorEntries j = (actorRows j).map Vector.get := by
  have hf : (fun n : Fin 13 => fun i : Fin 112 => entry n.val i.val) =
      (Vector.get ∘ factorRows) := by
    funext n i
    exact (Janko4.GeneratorCertificates.get_ofFn (fun k : Fin 112 => entry n.val k.val) i).symm
  unfold actorEntries actorRows
  split
  · simp [literalEntry_get, literalRows]
  · rw [List.map_append, List.map_ofFn, hf, wordEntries_eq]

noncomputable def actorEntry (j : Fin 4) (a : ℕ) : Fin 112 → ℕ :=
  (actorEntries j).getD a (fun i => 2^i.val)

theorem actorEntry_eq (j : Fin 4) (a : ℕ) :
    actorEntry j a = ((actorRows j).getD a packedOne).get := by
  unfold actorEntry
  rw [actorEntries_eq]
  have h : (fun i : Fin 112 => 2^i.val) = packedOne.get := by
    funext i
    exact (Janko4.GeneratorCertificates.get_ofFn (fun i : Fin 112 => 2^i.val) i).symm
  rw [h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

noncomputable def fastKernelRow (x : ℕ) (m : Fin 8192) : ℕ :=
  (List.ofFn (fun i : Fin 13 => i)).foldl
    (fun r i => if m.val.testBit i.val then rowAction r (fun k => entry i.val k.val) else r) x

theorem rowAction_factor (x : ℕ) (n : Fin 13) :
    rowAction x (fun k => entry n.val k.val) = packedRow x (factorRows n) := by
  rw [rowAction_eq]
  exact fastRow_eq x n

theorem fastKernelRow_eq (x : ℕ) (m : Fin 8192) : fastKernelRow x m = kernelRow x m := by
  simp only [fastKernelRow, kernelRow, rowAction_factor]

/-- The child mask, the parent mask, and the actor index from the published arrays. -/
noncomputable def nodeTuple (k : Fin 11) (n : ℕ) : ℕ × ℕ × ℕ :=
  ((maskAt k n).val, (maskAt k (parentAt k n)).val, actorIndexAt k n)

/-- The same crossing-row arithmetic, with the three node entries as arguments. -/
noncomputable def Check (j : Fin 4) (v : ℕ × ℕ × ℕ) : Prop :=
  rowAction (rowAction (KernelSeparation.row v.2.1) (liftEntry j)) (actorEntry j v.2.2) =
    rowAction (fastKernelRow (actorEntry j v.2.2 0) (Fin.ofNat 8192 v.1)) (liftEntry j)

noncomputable instance (j : Fin 4) (v : ℕ × ℕ × ℕ) : Decidable (Check j v) := by
  unfold Check
  infer_instance

theorem rowAction_get (x : ℕ) (v : Vector ℕ 112) :
    rowAction x v.get = packedRow x v := rowAction_eq x v.get

theorem check_iff (k : Fin 11) (n : ℕ) :
    Check (fiberIndex k) (nodeTuple k n) ↔ PackedEdge k n := by
  have hm : Fin.ofNat 8192 (maskAt k n).val = maskAt k n := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (maskAt k n).isLt
  unfold Check nodeTuple
  dsimp only
  rw [hm]
  simp only [actorEntry_eq, liftEntry_eq, fastKernelRow_eq, rowAction_get]
  rfl

theorem fastTuple_eq (k : Fin 11) (n : ℕ) : fastTuple k n = nodeTuple k n := by
  simp only [fastTuple, nodeTuple, fastNodes_eq, maskAt, parentAt, actorIndexAt]
  rfl

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows
