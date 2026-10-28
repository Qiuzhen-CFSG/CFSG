module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.LinearThree.Interfaces
public import Theory.GroupAction.AutomorphismFixerTransport

/-!
# Conditional assembly of the intrinsic PSL₃ field-component fixer

The matrix calculation identifies the standard pointwise fixer of the subfield
root groups with the coefficient group fixing that field. For an involutory
coefficient automorphism its order is exactly two. Full standard-automorphism
coverage and placement of the actual embedded component then bound its full
fixer by two. Ambient transport retains the subgroup, and perfectness justifies
the derived endpoint even at n = 1.

The coverage and placement premises remain explicit. This module does not yet
establish the unconditional `ComponentFixerBound` for the linear-three family.
Source: Aschbacher–Smith 16.1.4(4), 16.1.7(3a), and 16.3.5, printed
pp.1171–1173 and 1178–1179 of `refs/quasithin.pdf` (1 March 2004 manuscript).
-/

public section
open scoped MatrixGroups
open Subgroup
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
open Matrix.PSL3.FieldComponentFixer
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.LinearThree
universe u

/-- The matrix fixer calculation and an actual component placement give the
requested uniform bound, conditional on precisely the two remaining inputs. -/
theorem componentFixerBound_of_rootPlacement
    (hcover : ∀ (F : Type) (_ : Field F) (_ : Finite F) (m : ℕ),
      1 < m → Nat.card F = 2 ^ m → Matrix.PSL3.OuterSolvable.standard F = ⊤)
    (hplace : RootPlacement.{u}) : ComponentFixerBound.{u} FieldFamily.linearThree := by
  intro S hS hfin hsimple hperfect n hn hmodel a ha P hP hZ hsmall
  have hs := (derivedAt_iff_isPSL (S := P ⧸ center P) (2 ^ n)).mp hsmall
  obtain ⟨F, hF, hFfin, hchar, hq, e, σ, hσ, hroots⟩ :=
    hplace S n hn hmodel a ha P hP hZ hs
  have hbound : Nat.card (fixingSubgroup (MulAut PSL(3,F))
      (fieldRoots σ : Set PSL(3,F))) = 2 :=
    (card_fixer_fieldRoots (hcover F hF hFfin (2 * n) (by omega) hq) σ).trans hσ
  have hle : fixingSubgroup (MulAut PSL(3,F)) (P.map e.toMonoidHom : Set PSL(3,F)) ≤
      fixingSubgroup (MulAut PSL(3,F)) (fieldRoots σ : Set PSL(3,F)) :=
    fixingSubgroup_antitone (MulAut PSL(3,F)) PSL(3,F) hroots
  have hc := Subgroup.card_le_of_le hle
  rw [MulAut.card_fixingSubgroup_map e P, hbound] at hc
  exact lt_of_le_of_lt hc (by decide)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.LinearThree
