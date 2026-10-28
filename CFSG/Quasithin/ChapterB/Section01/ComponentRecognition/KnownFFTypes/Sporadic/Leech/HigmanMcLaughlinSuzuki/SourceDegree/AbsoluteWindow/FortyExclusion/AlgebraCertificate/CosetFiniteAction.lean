module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.Columns
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.Tables

/-!
# The finite table comparison for the universal HS norm module

The published right-coset table is converted to Lean's left action by inverting
its B transition (A is involutory). A breadth-first word labels each coordinate,
read in reverse order for the left action. Every remaining comparison is the
literal assertion `representative(next)⁻¹ * generator * representative ∈ P`.
Thus `points_intertwine` uses precisely the original order-512 subgroup and the
fixed seed of the original left-ideal quotient.

This module proves the reduction from these Schreier memberships and a small
finite norm quotient to the original certificate. Neither finite premise is
proved here. The data and the failed/completed diagnostic checks are recorded
in `CosetFiniteAction/source/README.md`; diagnostics are not proof oracles.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS case; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction

/-- Read low bits first. Appending a right-action letter to a GAP word prepends
its inverse-permutation generator to the corresponding Lean left-action word. -/
def decodeWord : ℕ → List (Fin 2)
  | 0 => []
  | 1 => []
  | n + 2 => ⟨(n + 2) % 2, Nat.mod_lt _ (by decide)⟩ :: decodeWord ((n + 2) / 2)
termination_by n => n

noncomputable def representative (i : Tables.Index) : KnownSimple.SporadicName.hs.Carrier :=
  ((decodeWord (Tables.wordCode i)).map generator).prod

noncomputable def point (i : Tables.Index) : CosetNormModule :=
  cosetNormRepresentation (representative i) (cosetNormVector 1)

theorem wordCode_zero : Tables.wordCode 0 = 1 := by decide +kernel

theorem point_zero : point 0 = cosetNormVector 1 := by
  simp [point, representative, wordCode_zero, decodeWord]

/-- This is membership in the published P, not in a conjugate marking.
All inverse and multiplication conventions are literal carrier operations. -/
def SchreierCondition : Prop := ∀ (s : Fin 2) (i : Tables.Index),
  (representative (Tables.transition s i))⁻¹ * generator s * representative i ∈ twoSubgroup

theorem points_intertwine (h : SchreierCondition) (s : Fin 2) (i : Tables.Index) :
    cosetNormRepresentation (generator s) (point i) = point (Tables.transition s i) := by
  let p : twoSubgroup := ⟨_, h s i⟩
  have hp : generator s * representative i = representative (Tables.transition s i) * p.val := by
    simp [p, mul_assoc]
  change cosetNormRepresentation (generator s)
      (cosetNormRepresentation (representative i) (cosetNormVector 1)) = _
  rw [← Module.End.mul_apply, ← map_mul, hp, map_mul, Module.End.mul_apply,
    cosetNorm_seed_fixed]
  rfl

/-- The finite rank computation and the exact Schreier comparisons are
independent. Both are still required for the unconditional dimension bound. -/
theorem universal_finrank_le (h : SchreierCondition) :
    Module.finrank (ZMod 2) CosetNormModule ≤
      Module.finrank (ZMod 2) (NormQuotient Tables.transition) :=
  finrank_le_quotient Tables.transition point 0 point_zero (points_intertwine h)

/-- Apply a completed finite quotient calculation to the original constructor,
retaining the independent kernel-nilpotence premise from CosetKernelNilpotence. -/
noncomputable def of_table_bound (h : SchreierCondition)
    (hd : Module.finrank (ZMod 2) (NormQuotient Tables.transition) < 40)
    (r : ℕ)
    (hr : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, cosetNormRepresentation.asAlgebraHom x = 0) →
        xs.prod ∈ fiveNormIdeal) : NormCertificate :=
  of_quotient_bound Tables.transition point 0 point_zero (points_intertwine h) hd r hr

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
