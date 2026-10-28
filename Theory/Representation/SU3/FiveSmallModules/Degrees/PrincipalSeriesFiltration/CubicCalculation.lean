module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.Model
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.CharacterParameters
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.PairTransport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FieldTransport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FactorSimplicity

/-!
# The cubic principal-series filtration for SU₃(5)

Finite fields of order 25 are isomorphic. Fifth powers ensure that this
isomorphism preserves the stored involutions; entrywise transport identifies
the standard group and its actual root-and-torus Borel. Pulling the original
character back gives an explicit equivariant equivalence of the literal
induction quotients over the unchanged coefficient field.

The fixed GF(25) calculation supplies the image/kernel flag of a rank-21
square-zero intertwiner, with literal quotient dimensions 21, 84, 21.
The completed matrix-density certificates prove simplicity of these same
quotient actions over every original coefficient field. Applying the field
and induction transport therefore proves the unconditional
`cubic_principal_series_filtrations` theorem, with no additional model,
certificate or coefficient-field embedding premise.

Source: Guralnick–Malle, Proposition 4.3, p.10; Aschbacher–Smith K.2, p.453.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
universe u v
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A calculation on the fixed matrix-field model suffices for every
original field and involution, with no hypothesis on the original Gram matrix. -/
theorem cubic_principal_series_filtrations_of_model (hmodel : ModelFiltrations.{v}) :
    CubicPrincipalSeriesFiltrations.{u, v} := by
  intro F _ _ J hF hconj K _ _ _ χ hχ hcube
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype MatrixField := Fintype.ofFinite MatrixField
  let e : MatrixField ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact GaloisField.card 5 2 (by decide))
  have hc (x : MatrixField) : e (modelForm.conj x) = J.conj (e x) := by
    rw [modelForm_conj, hconj, map_pow]
  let eg := standardFieldEquiv modelForm J e hc
  let eb := standardBorelFieldEquiv modelForm J e hc
  let ψ : standardBorel modelForm →* Kˣ := χ.comp eb.toMonoidHom
  have hψ : ψ ≠ 1 := by
    intro he
    apply hχ
    apply MonoidHom.ext
    intro b
    obtain ⟨a, rfl⟩ := eb.surjective b
    exact DFunLike.congr_fun he a
  have hψcube (b : standardBorel modelForm) : ψ b ^ 3 = 1 := hcube (eb b)
  exact inductionPair_filtration _ _ eg eb (fun b => (standardBorelFieldEquiv_coe modelForm J e hc b).symm)
    ψ χ (fun _ => rfl)
    {21, 84} (hmodel K ψ hψ hψcube)


/-- The actual source-contract consumer of the flag construction and the
irreducibility proof on that exact flag. Neither premise is discharged here. -/
theorem cubic_principal_series_filtrations_of_simple_flags (s : ModelFlags.{v})
    (hs : ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1),
      (s K χ hne hcube).Simple) : CubicPrincipalSeriesFiltrations.{u, v} :=
  cubic_principal_series_filtrations_of_model (model_filtrations_of_simple_flags s hs)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation

namespace Representation.SU3.FiveSmallModules.Degrees
universe u v

/-- Every nontrivial cubic principal series has an actual finite filtration
with simple quotient degrees in `{21, 84}`. The proved model flag and its
literal quotient simplicity discharge both inputs of the field-transport
assembly, retaining the original coefficient field and involution. -/
theorem cubic_principal_series_filtrations : CubicPrincipalSeriesFiltrations.{u, v} :=
  CubicCalculation.cubic_principal_series_filtrations_of_simple_flags
    CubicCalculation.model_flags CubicCalculation.model_flags_simple

end Representation.SU3.FiveSmallModules.Degrees
