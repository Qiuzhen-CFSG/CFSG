module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Checks

/-!
# Direct point trajectories for the class-B certificates

The action is proved equal to the original Held words before four-point
closure is used. These checks optimize reduction without adding assumptions.
Source: HeG1-P1.M and the retained HeG1-p2058B0 generator tables.
-/

@[expose] public section

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

def powerPoint (j : Fin 17) (p : Fin 2058) : Fin 2058 := point ⟨j.val, by omega⟩ p
def inversePowerPoint (j : Fin 17) (p : Fin 2058) : Fin 2058 :=
  point (inverseIndex ⟨j.val, by omega⟩) p

def wordPoint : Nat → Nat → Fin 2058 → Fin 2058
  | 0, _, p => point 18 p
  | n + 1, code, p => if code = 0 then point 18 p else
      point 17 (powerPoint (digit code) (wordPoint n (code / 32)
        (inversePowerPoint (digit code) (point 17 p))))

theorem wordPoint_eq (n code : Nat) (p : Fin 2058) :
    wordPoint n code p = fastWord n code p := by
  induction n generalizing code p with
  | zero => rfl
  | succ n ih =>
    simp only [wordPoint, fastWord]
    split
    · rfl
    · change point 17 (powerPoint (digit code) (wordPoint n (code / 32)
        (inversePowerPoint (digit code) (point 17 p)))) =
        point 17 (powerPoint (digit code) (fastWord n (code / 32)
        (inversePowerPoint (digit code) (point 17 p))))
      rw [ih]

def rowPoint (i : Fin 11025) (j : Fin 17) (p : Fin 2058) : Fin 2058 :=
  powerPoint j (wordPoint 5 (wordCode i) (inversePowerPoint j p))

theorem rowPoint_eq (i : Fin 11025) (j : Fin 17) (p : Fin 2058) :
    rowPoint i j p = fastRow i j p := by
  change powerPoint j (wordPoint 5 (wordCode i) (inversePowerPoint j p)) =
    powerPoint j (fastWord 5 (wordCode i) (inversePowerPoint j p))
  rw [wordPoint_eq]

def closureCheck (i : Fin 11025) : Bool :=
  (List.range 17).all fun j =>
    let j : Fin 17 := ⟨j % 17, Nat.mod_lt _ (by decide)⟩
    (List.range 4).all fun t =>
      let p : Fin 2058 := ⟨t % 2058, Nat.mod_lt _ (by decide)⟩
      point 17 (rowPoint i j (point 17 p)) == rowPoint (edgeIndex i j) (edgePower i j) p

theorem closureCheck_sound (i : Fin 11025) (h : closureCheck i = true) : ClosedAt i := by
  intro j t
  change point 17 (fastRow i j (point 17 ⟨t.val, by omega⟩)) =
    fastRow (edgeIndex i j) (edgePower i j) ⟨t.val, by omega⟩
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt))
    t.val (List.mem_range.mpr t.isLt)
  have ht : t.val < 2058 := by omega
  simpa only [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt ht, beq_iff_eq,
    rowPoint_eq] using hh

/-- A bounded closure-only check, for independently certified ranges. -/
def closureBlock (start count : Nat) : Bool :=
  (List.range count).all (fun j => closureCheck
    ⟨(start + j) % 11025, Nat.mod_lt _ (by decide)⟩)

theorem closureBlock_sound {start count : Nat} (h : closureBlock start count = true)
    (i : Fin 11025) (hi : start ≤ i.val ∧ i.val < start + count) : ClosedAt i := by
  have he : start + (i.val - start) = i.val := by omega
  have hh := List.all_eq_true.mp h (i.val - start) (List.mem_range.mpr (by omega))
  apply closureCheck_sound
  simpa only [he, Nat.mod_eq_of_lt i.isLt] using hh

def trajectoryBlock (start count : Nat) : Bool :=
  (List.range count).all (fun j =>
    let i : Fin 11025 := ⟨(start + j) % 11025, Nat.mod_lt _ (by decide)⟩
    closureCheck i && decide (RejectedAt i))

theorem trajectoryBlock_sound {start count : Nat} (h : trajectoryBlock start count = true)
    (i : Fin 11025) (hi : start ≤ i.val ∧ i.val < start + count) :
    ClosedAt i ∧ RejectedAt i := by
  have he : start + (i.val - start) = i.val := by omega
  have hh := List.all_eq_true.mp h (i.val - start) (List.mem_range.mpr (by omega))
  have hh' : closureCheck i = true ∧ RejectedAt i := by
    simpa only [he, Nat.mod_eq_of_lt i.isLt, Bool.and_eq_true, decide_eq_true_eq] using hh
  exact ⟨closureCheck_sound i hh'.1, hh'.2⟩

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
