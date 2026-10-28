module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.FactorSets

/-!
# The parity factor set for the two standard binary actions

The all-ones vector is fixed by the ordinary and twisted actions of S4.
Assign that vector to a pair of odd permutations, and the identity to every
other pair. The sign multiplication law proves the normalized cocycle identity.
This constructs two genuine groups on binary four-space times S4, with their
specified kernel inclusions and quotient maps from `FactorSets`.

These are proposed representatives for the nontrivial extension classes in the
finite extension step of Huppert--Blackburn, *Finite Groups III*, XII.1.18(b),
p.314. This module proves their group laws, without assuming completeness of
the two classes, nonsplitting, or identification with `NonsplitModels`.
-/

@[expose] public section

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
open LocalModelDichotomy AbelianExtension

/-- The fixed vector with all four binary coordinates equal to one. -/
def diagonal : BinaryFour := Multiplicative.ofAdd (fun _ => 1)

/-- The diagonal vector has square equal to the identity. -/
theorem diagonal_sq : diagonal * diagonal = 1 := by decide +kernel

/-- Coordinate permutations fix the diagonal vector. -/
theorem permutationAction_diagonal (s : SymmetricFour) :
    permutationAction s diagonal = diagonal := rfl

/-- The parity twist also fixes the diagonal vector. -/
theorem twistedAction_diagonal (s : SymmetricFour) :
    twistedAction s diagonal = diagonal := by
  have h : parityShear diagonal = diagonal := by decide +kernel
  change (if Equiv.Perm.sign s = 1 then permutationAction s
    else parityShear * permutationAction s) diagonal = diagonal
  split_ifs
  · rfl
  · exact h

/-- The diagonal carry when multiplying two odd permutations. -/
def parityCarry (s t : SymmetricFour) : BinaryFour :=
  if Equiv.Perm.sign s = 1 ∨ Equiv.Perm.sign t = 1 then 1 else diagonal

/-- The parity carry is a factor set for any action fixing the diagonal. -/
def parityFactorSet (α : SymmetricFour →* MulAut BinaryFour)
    (hfix : ∀ s, α s diagonal = diagonal) : FactorSet α where
  toFun := parityCarry
  one_left q := by simp [parityCarry]
  one_right q := by simp [parityCarry]
  cocycle q r s := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign q) with hq | hq <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign r) with hr | hr <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hs | hs <;>
      simp [parityCarry, map_mul, hq, hr, hs, hfix]

/-- The explicit parity factor set for the ordinary action. -/
def permutationFactorSet : FactorSet permutationAction :=
  parityFactorSet permutationAction permutationAction_diagonal

/-- The explicit parity factor set for the twisted action. -/
def twistedFactorSet : FactorSet twistedAction :=
  parityFactorSet twistedAction twistedAction_diagonal

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
