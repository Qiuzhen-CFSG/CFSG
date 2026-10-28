module

public import Theory.SpecificGroups.Janko3.Model.Order.Terminal
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Structure of the terminal J₃ stabilizer

The sixteen certified representatives form a copy of C₂ × D₈. A bijective
index table identifies the direct product with these representatives, and a
kernel check verifies multiplication on the sixteen indices. The already
proved `L2Step` identities lift this calculation to the concrete permutations.
Here `DihedralGroup 4` denotes the dihedral group of order eight.

Source: ATLAS J3G1-p6156B0 and the terminal words and transitions retained in
`Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate
open Theory.GroupTheory

-- Rows correspond to rotations and reflections, first in the identity C₂
-- coordinate and then in its nonidentity coordinate.
private def terminalIndex : Multiplicative (ZMod 2) × DihedralGroup 4 → Fin 16
  | (z, .r i) =>
    if z.toAdd = 0 then ![0, 1, 6, 4] i else ![7, 5, 9, 2] i
  | (z, .sr i) =>
    if z.toAdd = 0 then ![3, 8, 13, 11] i else ![14, 12, 15, 10] i

private theorem terminalIndex_bijective : Function.Bijective terminalIndex := by
  decide +kernel

private theorem terminalIndex_mul (x y : Multiplicative (ZMod 2) × DihedralGroup 4) :
    terminalIndex (x * y) = (L2RepWord (terminalIndex x)).foldr L2Act (terminalIndex y) := by
  have h : ∀ x y : Multiplicative (ZMod 2) × DihedralGroup 4,
      terminalIndex (x * y) = (L2RepWord (terminalIndex x)).foldr L2Act (terminalIndex y) := by
    decide +kernel
  exact h x y

private theorem evalWord_mul_rep (w : List (Fin 6)) (s : Fin 16) :
    evalWord L2Gen w * L2Rep s = L2Rep (w.foldr L2Act s) := by
  induction w with
  | nil => simp only [evalWord, one_mul, List.foldr_nil]
  | cons i w ih =>
    rw [evalWord, mul_assoc, ih, L2Step]
    rfl

private noncomputable def terminalRepEquiv : Fin 16 ≃ H2 :=
  Equiv.ofBijective (fun r => ⟨L2Rep r, L2Rep_mem r⟩) (by
    constructor
    · intro r s h
      apply L2Point_injective
      exact (L2Rep_point r).symm.trans
        ((congrArg (fun g : H2 => (g : Equiv.Perm (Fin 6156)) 2) h).trans (L2Rep_point s))
    · intro g
      obtain ⟨r, hr⟩ := H2_rep g
      exact ⟨r, Subtype.ext hr.symm⟩)

private noncomputable def terminalEquiv :
    Multiplicative (ZMod 2) × DihedralGroup 4 ≃ H2 :=
  (Equiv.ofBijective terminalIndex terminalIndex_bijective).trans terminalRepEquiv

/-- The concrete two-point stabilizer is C₂ × D₈. -/
public noncomputable def H2_mulEquiv : H2 ≃* Multiplicative (ZMod 2) × DihedralGroup 4 :=
  ({ terminalEquiv with
    map_mul' := by
      intro x y
      apply Subtype.ext
      change L2Rep (terminalIndex (x * y)) = L2Rep (terminalIndex x) * L2Rep (terminalIndex y)
      exact (congrArg L2Rep (terminalIndex_mul x y)).trans
        (evalWord_mul_rep (L2RepWord (terminalIndex x)) (terminalIndex y)).symm
    } : Multiplicative (ZMod 2) × DihedralGroup 4 ≃* H2).symm

end Sporadic.Janko3.OrderCertificate
