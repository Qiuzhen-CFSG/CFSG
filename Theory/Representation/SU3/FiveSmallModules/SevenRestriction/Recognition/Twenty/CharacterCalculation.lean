module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.CentralDescent
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.LocalInputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity

/-!
# Assembling the degree-twenty character calculation from Borel calculations

Every simple twenty-dimensional module over the original finite coefficient
field is absolute, has exactly the SU center as kernel, and has no root-center
invariants. In particular this applies to the supplied literal quotient of
trivial Borel induction; no simplicity after scalar extension is assumed.

The proved independent calculations compare restrictions to the actual Borel
and establish uniqueness of extension to SU₃(5). Their composite gives an actual whole-group
intertwiner, and hence the precise trace identity required by
`TwentyTraceComparison`. The conditional assembly is retained, and
`twenty_trace_comparison` discharges both local inputs over the original field.

Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

/-- The supplied simple quotient has the exact structural properties used by
both local calculations, without a splitting-field hypothesis. -/
theorem trivial_twenty_factor_structure
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K : Type v} [Field K] [Finite K] [CharP K 2]
    (S : Subrepresentation (ind (standardBorel J).subtype
      (scalarCharacter (1 : standardBorel J →* Kˣ))))
    (T : Subrepresentation S.toRepresentation)
    (hi : T.quotientRepresentation.IsIrreducible)
    (hd : Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20) :
    T.quotientRepresentation.IsAbsolutelyIrreducible ∧
      T.quotientRepresentation.ker = Subgroup.center (standardGroup J) ∧
      invariants (T.quotientRepresentation.comp (standardRootCenter J).subtype) = ⊥ := by
  let : FiniteDimensional K (S.toSubmodule ⧸ T.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by omega)
  let : T.quotientRepresentation.IsIrreducible := hi
  exact ⟨absolute_of_irreducible_twenty J hc hconj T.quotientRepresentation hd,
    irreducible_twenty_kernel_and_root_invariants J hc hconj T.quotientRepresentation hd⟩

private theorem trace_of_borel_calculations
    (hborel : TwentyBorelComparison.{v}) (hextension : TwentyBorelExtensionRigidity.{v})
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U W : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K (standardGroup J) U)
    (σ : Representation K (standardGroup J) W)
    (hi : τ.IsAbsolutelyIrreducible) (hs : σ.IsIrreducible)
    (hd : Module.finrank K U = 20) (hdim : Module.finrank K W = 20)
    (hz : invariants (τ.comp (standardRootCenter J).subtype) = ⊥) :
    τ.character = σ.character := by
  let : τ.IsAbsolutelyIrreducible := hi
  let : σ.IsIrreducible := hs
  have hτcenter := center_le_ker_of_absolute_twenty J hc hconj τ hd
  obtain ⟨hkernel, hroot⟩ := irreducible_twenty_kernel_and_root_invariants J hc hconj σ hdim
  have hσcenter : Subgroup.center (standardGroup J) ≤ σ.ker := hkernel.ge
  have hb := hborel F J hc hconj K U W τ σ hd hdim hτcenter hσcenter hz hroot
  obtain ⟨e⟩ := hextension F J hc hconj K U W τ σ hd hdim hτcenter hσcenter hz hroot hb
  exact char_iso e

/-- The local Borel comparison and the independent whole-group extension
calculation discharge the original trace contract, on its literal quotient. -/
theorem twenty_trace_comparison_of_borel_calculations
    (hborel : TwentyBorelComparison.{v})
    (hextension : TwentyBorelExtensionRigidity.{v}) : TwentyTraceComparison.{v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ τ _hk hi hd hz S T hs hdim
  let : FiniteDimensional K (S.toSubmodule ⧸ T.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by omega)
  exact trace_of_borel_calculations hborel hextension J hc hconj
    τ T.quotientRepresentation hi hs hd hdim hz

/-- Every representation in the degree-twenty recognition contract has the
same trace as each supplied simple degree-twenty quotient of trivial Borel
induction, on the original SU group and over the original coefficient field. -/
theorem twenty_trace_comparison : TwentyTraceComparison.{v} :=
  twenty_trace_comparison_of_borel_calculations
    twenty_borel_comparison twenty_borel_extension_rigidity

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
