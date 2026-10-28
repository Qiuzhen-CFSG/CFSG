module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.NativeInputs
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.HexadInputs

/-!
# Native M22 hexad code clauses

The proved M24 octad dynamics, H.14 kernel coordinates, and quintet fixed
dimensions instantiate the complete hexad code assembly. In particular the
five-dimensional commutator has its natural four-dimensional section, its
quotient is the six-point permutation core, and its kernel action consists of
all transvections with the actual fixed line as center. The quintet crossing
and fixed quotient use these same literal subspaces.

Source: Aschbacher--Smith H.16.4(1--5), printed p.403; the native module
inputs to 8.2.11--12, printed p.722, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeSource

abbrev restriction : OuterRestrictionInput m22SourceOctad := M22ChapterH.Hexad.outerRestriction
abbrev ambientFixed : AmbientFixedInput m22SourceOctad :=
  CocodeLocal.hexadAmbientFixedInput m22SourceOctad

/-- All intermediate cocode witnesses now have their native producers. -/
def actionData : CocodeActionData (BinaryPermutation.natural (Fin 6)) :=
  Assembly.cocodeActionData restriction ambientFixed
    (CocodeLocal.hexadAmbientTransvectionInput m22SourceOctad) NativeInputs.kernelConjugation

def kernelModel : KernelModel actionData :=
  Assembly.kernelModel restriction ambientFixed
    (CocodeLocal.hexadAmbientTransvectionInput m22SourceOctad) NativeInputs.kernelConjugation

/-- H.16.4, with every earlier native module input discharged. -/
theorem code_clauses :
    CodeChiefActions actionData restriction ambientFixed ∧
      Module.finrank (ZMod 2) quintetFixedAnnihilator = 9 ∧
      codeCommutator Kernel ≤ quintetFixedAnnihilator ∧
      ¬ codeCommutator Kernel ≤
        fixedSpace m22OuterCodeRepresentation (m22OuterQuintetKernel m22SourceSextet) ∧
      fixedCodeQuotient = commutatorImage :=
  Assembly.code_clauses restriction ambientFixed
    (CocodeLocal.hexadAmbientTransvectionInput m22SourceOctad)
    NativeInputs.kernelConjugation NativeInputs.quintetDimensions

/-- The commutator five-space used in 8.2.11. -/
theorem commutator_finrank : Module.finrank (ZMod 2) (codeCommutator Kernel) = 5 := by
  rw [← codeCommutatorSubrepresentation_space]
  exact code_clauses.1.dimensions.2.1

/-- Natural coordinates on the literal commutator modulo its fixed line. -/
def naturalFourEquiv :
    (V5.toSubmodule ⧸ codeCenter.toSubmodule) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  (actionData.middleEquiv restriction ambientFixed).trans kernelModel.dualNaturalEquiv

theorem naturalFourEquiv_equivariant (g : Stabilizer)
    (v : V5.toSubmodule ⧸ codeCenter.toSubmodule) :
    naturalFourEquiv (codeCenter.quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (NativeInputs.kernelConjugation.quotientMap g) (naturalFourEquiv v) :=
  (congrArg kernelModel.dualNaturalEquiv
    (actionData.middleEquiv_equivariant restriction ambientFixed g v)).trans
      (kernelModel.dualNaturalEquiv_equivariant g _)

/-- Restriction to native M22 gives the source's natural A6 action. -/
theorem naturalFourEquiv_inner_equivariant (g : M22ChapterH.Hexad.Action.Inner)
    (v : V5.toSubmodule ⧸ codeCenter.toSubmodule) :
    naturalFourEquiv
        (codeCenter.quotientRepresentation (M22ChapterH.Hexad.Action.innerToOuter g) v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (M22ChapterH.Hexad.Action.Natural.innerMap g) (naturalFourEquiv v) :=
  (naturalFourEquiv_equivariant (M22ChapterH.Hexad.Action.innerToOuter g) v).trans
    (congrArg (fun s : Equiv.Perm (Fin 6) =>
      BinaryPermutation.naturalRepresentation (Fin 6) s (naturalFourEquiv v))
      (M22ChapterH.Hexad.Action.Natural.maps_compatible g))

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeSource
