module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Transitions.Evaluation
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.CoverageReduction
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Soundness of point checks for the Held local transitions

The factor lists consist of positive letters. The certified local permutations
and word evaluator therefore compute their actual Held action. The four-point
base then converts each point check into the required equality in Held.
Source: the fixed factors in `SubgroupCover/source/factors.json`.
-/

set_option maxRecDepth 8192

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionChecks

def evenImage (i : Bool) (k : Fin 4) (x : Fin 2058) : Fin 2058 :=
  localAct i (twoWord i 0 k) x

theorem evenImage_eq (i : Bool) (k : Fin 4) (x : Fin 2058) :
    evenImage i k x = representation (evenGenerator i k) x :=
  localAct_eq _ _ _

private theorem right_positive (i : Bool) :
    ∀ r : Fin 135, ∀ t ∈ (rightData i r).2, t.2 = 1 := by
  cases i <;> decide +kernel

private theorem transition_positive (i : Bool) :
    ∀ (r : Fin 135) (k : Fin 2),
      ∀ t ∈ (transition i r (k.castLE (by decide))).2, t.2 = 1 := by
  cases i <;> decide +kernel

def rightAct (i : Bool) (r : Fin 135) (x : Fin 2058) : Fin 2058 :=
  localAct i (representativeWord i (rightData i r).1)
    (positiveAct (evenImage i) (rightData i r).2 x)

theorem rightAct_eq (i : Bool) (r : Fin 135) (x : Fin 2058) :
    rightAct i r x = representation (rightRepresentative i r) x := by
  unfold rightAct
  rw [positiveAct_eq _ _ (evenImage_eq i) _ (right_positive i r), localAct_eq]
  rfl

def letterAct (i : Bool) (k : Fin 2) (x : Fin 2058) : Fin 2058 :=
  if k = 0 then standardPerm x else localPerm i x

theorem letterAct_eq (i : Bool) (k : Fin 2) (x : Fin 2058) :
    letterAct i k x = representation (localLetter i (k.castLE (by decide))) x := by
  match k with
  | 0 => exact congrArg (fun p : Equiv.Perm (Fin 2058) => p x) standardPerm_eq
  | 1 => exact congrArg (fun p : Equiv.Perm (Fin 2058) => p x) (localPerm_eq i)

/-- Four point computations for one positive transition. -/
def pointCheck (i : Bool) (r : Fin 135) (k : Fin 2) : Prop :=
  ∀ x : Fin 4,
    rightAct i r (letterAct i k ⟨x.val, by omega⟩) =
      positiveAct (evenImage i) (transition i r (k.castLE (by decide))).2
        (rightAct i (transition i r (k.castLE (by decide))).1 ⟨x.val, by omega⟩)

theorem transition_of_pointCheck (i : Bool) (r : Fin 135) (k : Fin 2)
    (h : pointCheck i r k) :
    rightRepresentative i r * localLetter i (k.castLE (by decide)) =
      evalPowers (evenGenerator i) (transition i r (k.castLE (by decide))).2 *
        rightRepresentative i (transition i r (k.castLE (by decide))).1 := by
  apply eq_of_four_point_images
  intro x
  have hx := h x
  rw [letterAct_eq, rightAct_eq, rightAct_eq,
    positiveAct_eq _ _ (evenImage_eq i) _ (transition_positive i r k)] at hx
  simpa only [map_mul, Equiv.Perm.mul_apply] using hx

def rowIndex (b : Fin 17) (r : Fin 8) : Fin 135 :=
  ⟨(8 * b.val + r.val) % 135, Nat.mod_lt _ (by decide)⟩

/-- A Boolean traversal keeps finite enumeration out of dependent proof reduction. -/
def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun j => if h : j < n then f ⟨j, h⟩ else false)

theorem of_checkFin {n : ℕ} (f : Fin n → Bool) (h : checkFin f = true)
    (j : Fin n) : f j = true := by
  have hj := List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt)
  simpa only [j.isLt, dite_true] using hj

/-- Eight consecutive representatives, with the final surplus row wrapped to zero. -/
def blockCheck (i : Bool) (b : Fin 17) : Bool :=
  checkFin fun r : Fin 8 => checkFin fun k : Fin 2 => checkFin fun x : Fin 4 =>
    decide (rightAct i (rowIndex b r) (letterAct i k ⟨x.val, by omega⟩) =
      positiveAct (evenImage i) (transition i (rowIndex b r) (k.castLE (by decide))).2
        (rightAct i (transition i (rowIndex b r) (k.castLE (by decide))).1
          ⟨x.val, by omega⟩))

theorem blockCheck_sound (i : Bool) (b : Fin 17) (h : blockCheck i b = true)
    (r : Fin 8) (k : Fin 2) : pointCheck i (rowIndex b r) k := by
  intro x
  exact of_decide_eq_true (of_checkFin _ (of_checkFin _ (of_checkFin _ h r) k) x)

theorem all_of_blocks (i : Bool) (h : ∀ b, blockCheck i b = true) :
    ∀ (r : Fin 135) (k : Fin 2), pointCheck i r k := by
  intro r k
  let b : Fin 17 := ⟨r.val / 8, by omega⟩
  let s : Fin 8 := ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩
  have hr : rowIndex b s = r := by
    apply Fin.ext
    dsimp [rowIndex, b, s]
    omega
  rw [← hr]
  exact blockCheck_sound i b (h b) s k

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionChecks
