module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.Values

/-!
# Agreement of the packed certificates with the original matrices

The entrywise checks identify the packed data with precisely the transposes
specified in Data.lean. Explicit decision procedures avoid higher-order
instance synthesis on the two equal-sized index types; all checking still
uses kernel reduction. Source: the original ModelFlag/source diagnostics for
Guralnick–Malle, Proposition 4.3, p.10.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.Certificate
open Packed

private instance nilpotentAgreementDecision : Decidable (∀ (i j : Fin 126),
    matrix 126 N i j = rawNilpotent.transpose i j) :=
  @Nat.decidableForallFin 126 _ (fun _i =>
    @Nat.decidableForallFin 126 _ (fun _j => inferInstance))

private instance generatorAgreementDecision : Decidable (∀ (a : Fin 2) (i j : Fin 126),
    matrix 126 (G a) i j = (rawGenerator a).transpose i j) :=
  @Nat.decidableForallFin 2 _ (fun _a =>
    @Nat.decidableForallFin 126 _ (fun _i =>
      @Nat.decidableForallFin 126 _ (fun _j => inferInstance)))

theorem nilpotent_agreement : matrix 126 N = rawNilpotent.transpose := by
  apply Matrix.ext
  decide +kernel

theorem generator_agreement (a : Fin 2) : matrix 126 (G a) = (rawGenerator a).transpose := by
  have h : ∀ (a : Fin 2) (i j : Fin 126),
      matrix 126 (G a) i j = (rawGenerator a).transpose i j := by decide +kernel
  exact Matrix.ext (h a)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.Certificate
