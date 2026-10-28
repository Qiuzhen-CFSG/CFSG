module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Tables

/-!
# Soundness of Held column 1 row checks

Signed representative words and positive marked-subgroup words are evaluated
as functions using the checked generator tables. Equality on the four-point
base implies actual equality in Held. The batch soundness theorem preserves
the exact row convention `2*j + e`; it requires a kernel-checked batch.

Source: `DoubleCosets/source/README.md` and `Held.eq_of_four_point_images`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1Certificate
open Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

@[expose] public def repAction (j : Fin 4831) : Fin 2058 → Fin 2058 :=
  wordAction (packedAction packA) (packedAction packA) (packedAction packB)
    (packedAction packBi) (fastRepresentativeWord j)

public theorem repAction_eq (j : Fin 4831) (t : Fin 2058) :
    repAction j t = representation (representative j) t := by
  rw [representation_representative]
  change wordAction fastA (fastA⁻¹ : Equiv.Perm (Fin 2058)) fastB
    (fastB⁻¹ : Equiv.Perm (Fin 2058)) _ t = _
  rw [wordAction_eq, fastA_eq, fastB_eq]

@[expose] public def positiveAction : List (Fin 4) → Fin 2058 → Fin 2058
  | [], t => t
  | g :: w, t => genAction g (positiveAction w t)

private theorem positiveAction_eq (w : List (Fin 4)) (t : Fin 2058) :
    positiveAction w t = representation ((w.map markedGenerator).prod) t := by
  induction w generalizing t with
  | nil => simp only [positiveAction, List.map_nil, List.prod_nil, map_one,
      Equiv.Perm.one_apply]
  | cons g w ih => simp only [positiveAction, List.map_cons, List.prod_cons,
      map_mul, Equiv.Perm.mul_apply, genAction_eq, ih]

@[expose] public def subAction (j : Fin 1024) : Fin 2058 → Fin 2058 :=
  positiveAction (subgroupWord j)

public theorem subAction_eq (j : Fin 1024) (t : Fin 2058) :
    subAction j t = representation (subgroupElement j) t := by
  unfold subAction subgroupElement
  exact positiveAction_eq (subgroupWord j) t

@[expose] public def moveAction : Fin 2058 → Fin 2058 :=
  wordAction (packedAction packA) (packedAction packA) (packedAction packB)
    (packedAction packBi) (moveWord 1)

public theorem moveAction_eq (t : Fin 2058) :
    moveAction t = representation (move 1) t := by
  rw [representation_move]
  change wordAction fastA (fastA⁻¹ : Equiv.Perm (Fin 2058)) fastB
    (fastB⁻¹ : Equiv.Perm (Fin 2058)) _ t = wordEval atlasA atlasB _ t
  rw [wordAction_eq, fastA_eq, fastB_eq]

@[expose] public def midAction (e : Bool) (t : Fin 2058) : Fin 2058 :=
  if e then genAction 0 t else t

public theorem midAction_eq (e : Bool) (t : Fin 2058) :
    midAction e t = representation (middle 1 e) t := by
  cases e
  · rfl
  · exact genAction_eq 0 t

/-- A row checks precisely the four points of the proved Held base. -/
@[expose] public def check (j : Fin 4831) (e : Bool) (k : Fin 4831)
    (l r : Fin 1024) : Bool :=
  (List.range 4).all fun p =>
    repAction j (midAction e (moveAction ⟨p % 2058, Nat.mod_lt _ (by decide)⟩)) ==
    subAction l (repAction k (subAction r ⟨p % 2058, Nat.mod_lt _ (by decide)⟩))

private theorem representation_mul_three (x y z : He) (t : Fin 2058) :
    representation (x * y * z) t = representation x (representation y (representation z t)) := by
  simp only [map_mul, Equiv.Perm.mul_apply]

set_option maxRecDepth 8192 in
/-- The Boolean check certifies an actual factorization with subgroup factors. -/
public theorem covered_of_check (j : Fin 4831) (e : Bool) (k : Fin 4831)
    (l r : Fin 1024) (h : check j e k l r = true) :
    Theory.GroupTheory.DoubleCosetTransitions.Covered markedSubgroup representative
      (representative j * middle 1 e * move 1) := by
  refine ⟨k, subgroupElement l, subgroupElement r,
    subgroupElement_mem l, subgroupElement_mem r, ?_⟩
  apply Held.eq_of_four_point_images
  intro p
  have hp : p.val < 2058 := by omega
  have heq := List.all_eq_true.mp h p.val (List.mem_range.mpr p.isLt)
  have heq' := beq_iff_eq.mp heq
  have hp' : (⟨p.val % 2058, Nat.mod_lt _ (by decide)⟩ : Fin 2058) =
      ⟨p.val, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
  rw [hp'] at heq'
  simp only [repAction_eq, midAction_eq, moveAction_eq, subAction_eq] at heq'
  exact (representation_mul_three (representative j) (middle 1 e) (move 1) ⟨p.val, hp⟩).trans
    (heq'.trans (representation_mul_three (subgroupElement l) (representative k)
      (subgroupElement r) ⟨p.val, hp⟩).symm)


/-- A bounded batch of consecutive rows, numbered as `2*j + e`. -/
@[expose] public def checkRows (start count : ℕ)
    (data : Array (Fin 4831 × Fin 1024 × Fin 1024)) : Bool :=
  (List.range count).all fun n =>
    check ⟨((start + n) / 2) % 4831, Nat.mod_lt _ (by decide)⟩
      ((start + n) % 2 == 1) (data[n]!).1 (data[n]!).2.1 (data[n]!).2.2

public theorem covered_of_checkRows (start count : ℕ)
    (data : Array (Fin 4831 × Fin 1024 × Fin 1024))
    (h : checkRows start count data = true) (j : Fin 4831) (e : Bool)
    (hlo : start ≤ 2 * j.val + e.toNat)
    (hhi : 2 * j.val + e.toNat < start + count) :
    Theory.GroupTheory.DoubleCosetTransitions.Covered markedSubgroup representative
      (representative j * middle 1 e * move 1) := by
  let n := 2 * j.val + e.toNat - start
  have hn : n < count := by dsimp [n]; omega
  have hrow := List.all_eq_true.mp h n (List.mem_range.mpr hn)
  have he : start + n = 2 * j.val + e.toNat := by dsimp [n]; omega
  have hj : ((start + n) / 2) % 4831 = j.val := by
    rw [he]
    cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hb : ((start + n) % 2 == 1) = e := by
    rw [he]
    cases e <;> simp [Bool.toNat, Nat.add_mod]
  have hfin : (⟨((start + n) / 2) % 4831, Nat.mod_lt _ (by decide)⟩ : Fin 4831) = j :=
    Fin.ext hj
  rw [hfin, hb] at hrow
  exact covered_of_check j e _ _ _ hrow

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1Certificate
