module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.Transversal
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.Certificate
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.Model

/-!
# From finite group transitions to the actual cubic principal series

A `GroupCertificate` and the explicit canonical coset count construct the
requested `Coordinates χ` for every original characteristic-two coefficient
field. The count makes the 126 distinct representatives complete. Their
induction generators form the specified coordinates, and each checked
root–torus transition yields the corresponding transposed monomial matrix
for the inverse actor and inverse Borel character.

The checked finite group certificate supplies these identities in the literal
canonical group. `model_coordinates_of_canonical_card` therefore constructs
the uniform comparison with only the canonical coset count as a premise.
The count is discharged by the independent coset-cardinality theorem in the
parent flag construction. Source motivation: Guralnick–Malle, Proposition 4.3,
p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
open scoped Classical
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
universe v
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace GroupCertificate
variable (d : GroupCertificate)

theorem cover_of_canonical_card
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126) :
    ∀ g : standardGroup modelForm, ∃ i, ∃ b : standardBorel modelForm,
      g = b * d.representative i := by
  apply RightCoordinates.cover_of_card (standardBorel modelForm) d.representative d.separates
  simpa only [Nat.card_fin] using hcard

theorem inverse_generates :
    Subgroup.closure (Set.range fun a => (d.generator a)⁻¹) = ⊤ := by
  apply top_unique
  rw [← d.generates]
  apply (Subgroup.closure_le (K := _)).mpr
  rintro _ ⟨a, rfl⟩
  change d.generator a ∈ Subgroup.closure (Set.range fun a => (d.generator a)⁻¹)
  have h := (Subgroup.closure (Set.range fun a => (d.generator a)⁻¹)).inv_mem
    (Subgroup.subset_closure (Set.mem_range_self a))
  simpa only [inv_inv] using h

/-- The actual quotient comparison obtained from the finite group identities. -/
def coordinates (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) :
    Coordinates χ := by
  let hcover := d.cover_of_canonical_card hcard
  let e := RightCoordinates.equiv (standardBorel modelForm) χ d.representative d.separates hcover
  let hz := d.scalar_quadratic χ hne hcube
  refine ⟨d.scalar χ, hz, e, (fun a => (d.generator a)⁻¹), d.inverse_generates, ?_⟩
  intro a v
  have he : e.toLinearMap.comp (ind (standardBorel modelForm).subtype (scalarCharacter χ)
      (d.generator a)⁻¹) = (generatorMatrix (d.scalar χ) hz a).mulVecLin.comp e.toLinearMap := by
    apply RightCoordinates.hom_ext (standardBorel modelForm) χ d.representative hcover
    intro i x
    change e (ind (standardBorel modelForm).subtype (scalarCharacter χ) (d.generator a)⁻¹
        (IndV.mk (standardBorel modelForm).subtype (scalarCharacter χ) (d.representative i) x)) =
      (generatorMatrix (d.scalar χ) hz a).mulVec
        (e (IndV.mk (standardBorel modelForm).subtype (scalarCharacter χ) (d.representative i) x))
    dsimp only [e]
    rw [RightCoordinates.equiv_action_mk _ _ _ _ _ (d.generator a) i
      (generatorTarget a i) (d.factor a i) (d.transition a i), RightCoordinates.equiv_mk,
      generatorMatrix_single, d.factor_coefficient χ hz]
  exact LinearMap.congr_fun he v

@[simp] theorem coordinates_symm_apply
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1)
    (v : Fin 126 → K) :
    (d.coordinates hcard χ hne hcube).equiv.symm v =
      ∑ i, IndV.mk (standardBorel modelForm).subtype (scalarCharacter χ) (d.representative i) (v i) :=
  RightCoordinates.equiv_symm_apply (standardBorel modelForm) χ d.representative d.separates
    (d.cover_of_canonical_card hcard) v

@[simp] theorem coordinates_mk
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1)
    (i : Fin 126) (x : K) :
    (d.coordinates hcard χ hne hcube).equiv
      (IndV.mk (standardBorel modelForm).subtype (scalarCharacter χ) (d.representative i) x) =
      Pi.single i x :=
  RightCoordinates.equiv_mk (standardBorel modelForm) χ d.representative d.separates
    (d.cover_of_canonical_card hcard) i x

@[simp] theorem coordinates_mk_subgroup
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1)
    (i : Fin 126) (b : standardBorel modelForm) (x : K) :
    (d.coordinates hcard χ hne hcube).equiv
      (IndV.mk (standardBorel modelForm).subtype (scalarCharacter χ) ((b : standardGroup modelForm) * d.representative i) x) =
      Pi.single i ((χ b : K)⁻¹ * x) :=
  RightCoordinates.equiv_mk_subgroup (standardBorel modelForm) χ d.representative d.separates
    (d.cover_of_canonical_card hcard) i b x

end GroupCertificate

/-- Uniform comparison; construction of the finite group certificate remains required. -/
theorem model_coordinates_of_group_certificate
    (d : GroupCertificate) (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126) :
    ModelCoordinates.{v} := by
  intro K _ _ _ χ hne hcube
  exact ⟨d.coordinates hcard χ hne hcube⟩

/-- The literal cubic induction has the fixed monomial coordinates over every
original finite characteristic-two field. The canonical count supplies the
complete transversal and full generation in the checked finite certificate. -/
theorem model_coordinates_of_canonical_card
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126) :
    ModelCoordinates.{v} := by
  obtain ⟨d⟩ := group_certificate_of_canonical_card hcard
  exact model_coordinates_of_group_certificate d hcard

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
