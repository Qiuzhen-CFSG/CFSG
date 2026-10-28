module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.MatrixQuotient.Data
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables2
import Mathlib.Tactic.FinCases

/-!
# The finite max5 intertwining certificate

Two scalar checks on 2058 letters and the eight-vector matrix calculation
show that the literal max5 generators preserve the vector labels. Explicit
representatives prove surjectivity of the labeling. All finite calculations
are checked by the Lean kernel.

Source: the ATLAS data and discovery retained in `MatrixQuotient/Source`.
-/

namespace Held.RankOneLocalPair.MatrixQuotient
open TwoLocalCandidates.Cores

private theorem code_first : ∀ i : Fin 2058,
    colorCode (Tables2.p0 i) = codeAction 0 (colorCode i) := by
  apply allLetters
  decide +kernel

private theorem code_second : ∀ i : Fin 2058,
    colorCode (Tables2.p1 i) = codeAction 1 (colorCode i) := by
  apply allLetters
  decide +kernel

private theorem decode_action : ∀ k c,
    (generator k).toLin' (decode c) = decode (codeAction k c) := by
  decide +kernel

/-- The literal defining max5 elements act by the displayed binary matrices. -/
public theorem label_generator (k : Fin 2) (i : Fin 2058) :
    label (embedding 2 (localGenerator 2 k) i) = (generator k).toLin' (label i) := by
  fin_cases k
  · exact (congrArg (fun p : Equiv.Perm (Fin 2058) => label (p i)) Tables2.p0_eq).symm.trans
      ((congrArg decode (code_first i)).trans (decode_action 0 (colorCode i)).symm)
  · exact (congrArg (fun p : Equiv.Perm (Fin 2058) => label (p i)) Tables2.p1_eq).symm.trans
      ((congrArg decode (code_second i)).trans (decode_action 1 (colorCode i)).symm)

/-- Every binary vector labels an actual point of the Held permutation model. -/
public theorem label_surjective : Function.Surjective label := by
  have hd : ∀ v : Vector, ∃ c : Fin 8, decode c = v := by decide +kernel
  have hr : ∀ c, colorCode (colorRepresentative c) = c := by decide +kernel
  intro v
  obtain ⟨c, rfl⟩ := hd v
  exact ⟨colorRepresentative c, congrArg decode (hr c)⟩

end Held.RankOneLocalPair.MatrixQuotient
