module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Spaces
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Geometry
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Transfer

/-!
# The outer hexad code chief flag from the cocode action witnesses

Coordinate duality constructs the strict 1,5,6,10 flag, its four irreducible
factors, the full center transvections and both equivariant identifications.
The cubic argument identifies the quotient fixed space with V5/V1; its native
order-three displacement premise is discharged. The quintet hyperplane is the
annihilator of the actual cocode fixed line, and the marked tetrad calculation
proves the geometric comparison using the quintet fixed dimensions one and four.

The complete conditional theorem retains precisely the H.15.2 cocode action
witnesses, the earlier H.14 kernel module marking, the M24/H.14 restriction
inputs and the two stated quintet dimensions. Its source-theorem consumer
must construct these inputs. No code chiefness, action identification,
geometric incidence or quotient fixed-space conclusion is an input.

Source: Aschbacher--Smith, H.16.3 and H.16.4, printed p.403, combined
manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag

/-- The precise earlier quintet scalar inputs used in the geometric clause. -/
structure QuintetDimensions : Prop where
  cocode_fixed : Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation
    (m22OuterQuintetKernel m22SourceSextet)) = 1
  code_fixed : Module.finrank (ZMod 2) (fixedSpace m22OuterCodeRepresentation
    (m22OuterQuintetKernel m22SourceSextet)) = 4

/-- V9 defined by the actual quintet cocode fixed space. -/
def quintetFixedAnnihilator : Submodule (ZMod 2) M22Code :=
  annihilator (fixedSpace m22OuterCocodeRepresentation
    (m22OuterQuintetKernel m22SourceSextet))

theorem quintetFixedAnnihilator_eq (hQ : QuintetDimensions) :
    quintetFixedAnnihilator = quintetHyperplane := by
  unfold quintetFixedAnnihilator
  rw [quintet_fixed_eq_line hQ.cocode_fixed]
  rfl

/-- The complete geometric comparison in H.16.4(4), with the earlier quintet
dimension premises explicit and the code fixed space retained literally. -/
theorem geometric_comparison (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) (hQ : QuintetDimensions) :
    Module.finrank (ZMod 2) quintetFixedAnnihilator = 9 ∧
      codeCommutator Kernel ≤ quintetFixedAnnihilator ∧
      ¬ codeCommutator Kernel ≤ fixedSpace m22OuterCodeRepresentation
        (m22OuterQuintetKernel m22SourceSextet) := by
  rw [quintetFixedAnnihilator_eq hQ]
  exact ⟨quintetHyperplane_finrank, commutator_le_quintetHyperplane h,
    commutator_not_le_quintet_fixed h h24 hQ.code_fixed⟩

/-- All five clauses of H.16.4 for the literal outer code and intrinsic kernel,
conditional on the precise earlier cocode and group data. `CodeChiefActions`
includes the strict flag, dimensions, all four irreducible factors, full
transvections and the intertwining equations for the constructed equivalences.
The genuine S6 quotient is `D.symmetricQuotientEquiv`; its marking is kept
distinct from the earlier kernel marking in `K`. -/
theorem code_chief_flag {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (D : Actions.CocodeActionData E) (K : Actions.KernelModel D)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hQ : QuintetDimensions) :
    Actions.CodeChiefActions D h h24 ∧
      Module.finrank (ZMod 2) quintetFixedAnnihilator = 9 ∧
      codeCommutator Kernel ≤ quintetFixedAnnihilator ∧
      ¬ codeCommutator Kernel ≤ fixedSpace m22OuterCodeRepresentation
        (m22OuterQuintetKernel m22SourceSextet) ∧
      fixedCodeQuotient = commutatorImage := by
  obtain ⟨h9, h59, h54⟩ := geometric_comparison h h24 hQ
  exact ⟨Actions.code_chief_actions D K h h24, h9, h59, h54,
    D.fixedCodeQuotient_eq h h24⟩

end MathieuCode.Hexad.ChiefFlag
