module

public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.Spaces
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags

/-!
# The literal sextet code four-space and the centralizer correction

The native coordinate calculation identifies `codeSextetFixed` with the
annihilator of the within-tetrad cocode pair space. This gives its rank four
and recovers its full setwise stabilizer. Its pointwise centralizer is the
kernel of the actual action on the six tetrads, of order 192, properly
containing `sextetKernel`, of order 64.

This proves the fixed-space dimension in H.16.1(1) and the setwise assertion
used in H.16.6. It also disproves the intermediate pointwise-centralizer
equality printed in that proof; it does not disprove H.16.6 itself. The
remaining chief, residual, natural symplectic and transvection clauses
of H.16.1--2 remain separate obligations.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.16.1, printed p.402; proof of H.16.6, printed pp.404--405.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section13To16

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender

/-- A coordinate description of the literal source fixed space. -/
theorem codeSextetFixed_eq_annihilator (S : Sextet) :
    codeSextetFixed S =
      MathieuCode.CodeFlags.annihilator (⨆ B ∈ S.parts, MathieuCode.supportedPairSpace B) :=
  MathieuCode.CodeFlags.sextetCore_fixedSpace S

/-- The four-space dimension in H.16.1(1), with the intrinsic two-core. -/
theorem codeSextetFixed_finrank (S : Sextet) :
    Module.finrank (ZMod 2) (codeSextetFixed S) = 4 := by
  rw [codeSextetFixed_eq_annihilator]
  exact MathieuCode.CodeFlags.sextetCodeSpace_finrank S

/-- The exact ambient setwise stabilizer, proved by recovering the tetrads. -/
theorem codeSextetFixed_stabilizer (S : Sextet) :
    subspaceStabilizer MathieuCode.codeRepresentation (codeSextetFixed S) =
      sextetStabilizer S := by
  rw [codeSextetFixed_eq_annihilator]
  exact MathieuCode.CodeFlags.sextetCodeSpace_stabilizer S

/-- The actual ambient pointwise centralizer is the entire column kernel. -/
theorem codeSextetFixed_centralizer (S : Sextet) :
    subspaceKernel MathieuCode.codeRepresentation (codeSextetFixed S) ⊤ =
      (MathieuCode.sextetPartPerm S).ker.map (sextetStabilizer S).subtype := by
  rw [codeSextetFixed_eq_annihilator]
  exact MathieuCode.CodeFlags.sextetCodeSpace_centralizer S

theorem codeSextetFixed_centralizer_card (S : Sextet) :
    Nat.card (subspaceKernel MathieuCode.codeRepresentation (codeSextetFixed S) ⊤) = 192 := by
  rw [codeSextetFixed_eq_annihilator]
  exact MathieuCode.CodeFlags.sextetCodeSpace_centralizer_card S

/-- The extra centralizer requirement is false for the literal source space. -/
theorem codeSextetFixed_centralizer_ne_sextetKernel (S : Sextet) :
    subspaceKernel MathieuCode.codeRepresentation (codeSextetFixed S) ⊤ ≠ sextetKernel S :=
  MathieuCode.CodeFlags.sextet_fixed_centralizer_ne_core S

/-- The discrepancy is a strict containment, rather than a different marking. -/
theorem sextetKernel_lt_codeSextetFixed_centralizer (S : Sextet) :
    sextetKernel S < subspaceKernel MathieuCode.codeRepresentation (codeSextetFixed S) ⊤ :=
  MathieuCode.CodeFlags.sextetCore_lt_fixed_centralizer S

end CFSG.Quasithin.ChapterH.Section13To16
