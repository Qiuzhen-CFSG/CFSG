module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Chief

/-!
# Conditional hexad chief flag and dual actions

From the precise cocode action witnesses, the coordinate pairing constructs
V6 and the two required module equivalences. It identifies the full axis
radical with the full center radical on V5. The checked six-point invariant
subspace theorem gives the upper chief factor; an explicitly marked earlier
kernel model gives the middle factor. The one-dimensional factors are chief
by dimension. All actions use the actual outer representation and intrinsic
kernel at `m22SourceOctad`, and normality is relative to the hexad stabilizer.

This is the complete conditional implication for Aschbacher--Smith
H.16.4(1)--(3), printed p.403 (combined manuscript of 1 March 2004). The source
assembly must construct `CocodeActionData`, the earlier `KernelModel`, and
the earlier restriction and ambient fixed-space inputs. Clauses (4),(5) are
outside this module. In particular the two S6 markings are not identified
without an equivariant linear equivalence.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The actual code conclusions, including all four irreducible quotient factors
and intertwining equations for the explicitly constructed linear equivalences. -/
structure CodeChiefActions (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) : Prop where
  fixed_space : V1.toSubmodule = fixedSpace m22OuterCodeRepresentation Kernel
  commutator_space : V5.toSubmodule = codeCommutator Kernel
  strict : (⊥ : Subrepresentation codeAction) < V1 ∧ V1 < V5 ∧
    V5 < D.codeSix ∧ D.codeSix < ⊤
  dimensions : Module.finrank (ZMod 2) V1.toSubmodule = 1 ∧
    Module.finrank (ZMod 2) V5.toSubmodule = 5 ∧
    Module.finrank (ZMod 2) D.codeSix.toSubmodule = 6
  chief : (⊥ : Subrepresentation codeAction) ⋖ V1 ∧ V1 ⋖ V5 ∧
    V5 ⋖ D.codeSix ∧ D.codeSix ⋖ (⊤ : Subrepresentation codeAction)
  factors : IsIrreducible V1.toRepresentation ∧
    IsIrreducible codeCenter.quotientRepresentation ∧
    IsIrreducible (sectionSubrepresentation V5 D.codeSix).quotientRepresentation ∧
    IsIrreducible D.codeSix.quotientRepresentation
  faithful : Function.Injective codeKernelAction
  full : codeKernelAction.range = BinaryLinear.radical codeCenter.toSubmodule
  dual_kernel : ∀ g v, D.middleEquiv h h24 (codeCenter.quotientRepresentation g v) =
    D.kernelRepresentation.dual g (D.middleEquiv h h24 v)
  permutation_core : ∀ g v, D.quotientCoreEquiv (V5.quotientRepresentation g v) =
    BinaryPermutation.coreRepresentation (Fin 6) (D.quotientMap g) (D.quotientCoreEquiv v)

/-- H.16.4(1)--(3), conditional only on the stated cocode actions and genuine
earlier group/module inputs. No code action or irreducibility is assumed. -/
theorem code_chief_actions (D : CocodeActionData E) (K : KernelModel D)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    CodeChiefActions D h h24 where
  fixed_space := rfl
  commutator_space := codeCommutatorSubrepresentation_space
  strict := D.code_strict h h24
  dimensions := ⟨codeFixedSubrepresentation_finrank h,
    codeCommutatorSubrepresentation_finrank h h24, D.codeSix_finrank h h24⟩
  chief := D.code_chief K h h24
  factors := D.chief_factors_irreducible K h h24
  faithful := D.codeAction_faithful h h24
  full := D.codeAction_full h h24
  dual_kernel := D.middleEquiv_equivariant h h24
  permutation_core := D.quotientCoreEquiv_equivariant

end MathieuCode.Hexad.ChiefFlag.Actions
