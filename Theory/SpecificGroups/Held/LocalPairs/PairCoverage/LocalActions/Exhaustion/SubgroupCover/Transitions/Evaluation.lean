module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Data
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Local0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Local1

/-!
# Point evaluation of Held local words

Integer powers act by iteration on points, and positive factor words act by a
right fold. The lemmas identify these computations with the actual faithful
Held representation. This avoids constructing large nested permutation terms
in the transition certificates. No group order or coset index is used.

Sources: ATLAS HeG1-p2058B0 and max3W1/max4W1; the positive factors are
retained in `SubgroupCover/source/factors.json`.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionChecks
open RepresentativeImages

def natAct {α : Type*} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n+1, x => f (natAct f n x)

theorem natAct_eq {α : Type*} (p : Equiv.Perm α) (n : ℕ) (x : α) :
    natAct p n x = (p ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natAct, ih, pow_succ']; rfl

def intAct {α : Type*} (p : Equiv.Perm α) : ℤ → α → α
  | .ofNat n, x => natAct p n x
  | .negSucc n, x => natAct p.symm (n+1) x

theorem intAct_eq {α : Type*} (p : Equiv.Perm α) (n : ℤ) (x : α) :
    intAct p n x = (p ^ n) x := by
  cases n with
  | ofNat n =>
    change natAct p n x = (p ^ (n : ℤ)) x
    rw [zpow_natCast]
    exact natAct_eq p n x
  | negSucc n => simp only [intAct, natAct_eq, zpow_negSucc, ← inv_pow]; rfl

def wordAct {α β : Type*} (g : β → Equiv.Perm α) : List (β × ℤ) → α → α
  | [], x => x
  | t :: w, x => intAct (g t.1) t.2 (wordAct g w x)

theorem wordAct_eq {α β : Type*} (g : β → Equiv.Perm α)
    (w : List (β × ℤ)) (x : α) :
    wordAct g w x = (w.map (fun t => g t.1 ^ t.2)).prod x := by
  induction w with
  | nil => rfl
  | cons t w ih => rw [wordAct, intAct_eq, ih]; rfl

def localPerm (i : Bool) : Equiv.Perm (Fin 2058) :=
  if i then Local1.localPerm else Local0.localPerm

theorem localPerm_eq (i : Bool) : localPerm i = representation (localWord i) := by
  cases i
  · exact Local0.localPerm_eq
  · exact Local1.localPerm_eq

/-- Existing checked packed table for the standard involution. -/
def standardPerm : Equiv.Perm (Fin 2058) := Held.TwoLocalCandidates.Cores.Tables0.p0

theorem standardPerm_eq : standardPerm = atlasA := Held.TwoLocalCandidates.Cores.Tables0.p0_eq

def localAct (i : Bool) (w : List (Bool × ℤ)) (x : Fin 2058) : Fin 2058 :=
  wordAct (fun b => if b then localPerm i else standardPerm) w x

theorem localAct_eq (i : Bool) (w : List (Bool × ℤ)) (x : Fin 2058) :
    localAct i w x = representation (evalLocalWord i w) x := by
  rw [representation_evalLocalWord, ← localPerm_eq, ← standardPerm_eq]
  exact wordAct_eq _ _ _

def positiveAct (g : Fin 4 → Fin 2058 → Fin 2058) :
    List (Fin 4 × ℤ) → Fin 2058 → Fin 2058
  | [], x => x
  | t :: w, x => g t.1 (positiveAct g w x)

theorem positiveAct_eq (g : Fin 4 → Fin 2058 → Fin 2058) (h : Fin 4 → He)
    (hg : ∀ k x, g k x = representation (h k) x)
    (w : List (Fin 4 × ℤ)) (hw : ∀ t ∈ w, t.2 = 1) (x : Fin 2058) :
    positiveAct g w x = representation (evalPowers h w) x := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    have ht := hw t (List.mem_cons_self ..)
    have hw' : ∀ s ∈ w, s.2 = 1 := fun s hs => hw s (List.mem_cons_of_mem _ hs)
    change g t.1 (positiveAct g w x) = representation (h t.1 ^ t.2 * evalPowers h w) x
    rw [hg, ih hw', ht, zpow_one, map_mul]
    rfl

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionChecks
