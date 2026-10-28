module
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CharacterCoverage
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.Model

/-!
# Cubic parameters for actual Borel characters

Every character into a commutative group kills the actual root subgroup.
The root-and-torus definition of the Borel then shows that its characters
are determined by the torus, hence by one generating torus parameter.
A nontrivial character gives a nontrivial cubic scalar, satisfying
`z² + z + 1 = 0`. These identities hold in the original coefficient field.

This supplies the scalar parameter for uniform finite matrix certificates
in the principal-series approach to Guralnick–Malle, Proposition 4.3, p.10.
No parametrization or field embedding is assumed.
-/

public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
variable {F A : Type*} [Field F] [CommGroup A] (J : HermitianForm 3 F)

/-- Actual Borel characters are determined by their values on the full torus. -/
theorem character_eq_of_torus [CharP F 5] (χ ψ : standardBorel J →* A)
    (h : ∀ k : Fˣ, χ (principalTorusIn J k) = ψ (principalTorusIn J k)) : χ = ψ := by
  let N := χ.eqLocus ψ
  have hr : specialRoot (FormTransport.standardForm J) rfl ≤ N.map (standardBorel J).subtype := by
    rintro _ ⟨z, rfl⟩
    refine ⟨principalRootIn J z, ?_, rfl⟩
    change χ (principalRootIn J z) = ψ (principalRootIn J z)
    rw [borel_character_trivial_on_root J, borel_character_trivial_on_root J]
  have ht : specialTorus (FormTransport.standardForm J) rfl ≤ N.map (standardBorel J).subtype := by
    rintro _ ⟨k, rfl⟩
    exact ⟨principalTorusIn J k, h k, rfl⟩
  have hB : standardBorel J ≤ N.map (standardBorel J).subtype := sup_le hr ht
  apply MonoidHom.ext
  intro b
  obtain ⟨c, hc, he⟩ := hB b.property
  have hcb : c = b := Subtype.ext he
  subst c
  exact hc

/-- A generating torus parameter determines the entire Borel character. -/
theorem character_eq_of_generator [CharP F 5] (k : Fˣ)
    (hk : ∀ t : Fˣ, t ∈ Subgroup.zpowers k) (χ ψ : standardBorel J →* A)
    (h : χ (principalTorusIn J k) = ψ (principalTorusIn J k)) : χ = ψ := by
  apply character_eq_of_torus J
  intro t
  obtain ⟨n, rfl⟩ := hk t
  simp only [map_zpow, h]

/-- A nontrivial character has a nontrivial value on any generating parameter. -/
theorem character_generator_ne_one [CharP F 5] (k : Fˣ)
    (hk : ∀ t : Fˣ, t ∈ Subgroup.zpowers k) (χ : standardBorel J →* A)
    (hχ : χ ≠ 1) : χ (principalTorusIn J k) ≠ 1 := by
  intro h
  exact hχ (character_eq_of_generator J k hk χ 1 h)

/-- The precise scalar relation available to uniform cubic certificates. -/
theorem cubic_scalar_quadratic {K : Type*} [Field K] (z : Kˣ)
    (hne : z ≠ 1) (hcube : z ^ 3 = 1) : (z : K)^2 + (z : K) + 1 = 0 := by
  have h : (z : K) ≠ 1 := by
    intro h
    apply hne
    exact Units.ext h
  have hp : (z : K) ^ 3 = 1 := congrArg (fun x : Kˣ => (x : K)) hcube
  have he : ((z : K) - 1) * ((z : K)^2 + (z : K) + 1) = 0 := by
    calc
      _ = (z : K)^3 - 1 := by ring
      _ = 0 := by rw [hp]; ring
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h)

/-- Every original coefficient character admits a generating torus parameter
with a nontrivial cubic value, supplying the field-independent certificate parameter. -/
theorem exists_cubic_parameter [Finite F] (hF : Nat.card F = 5 ^ 2)
    {K : Type*} [Field K] [CharP K 2] (χ : standardBorel J →* Kˣ) (hχ : χ ≠ 1) :
    ∃ k : Fˣ, (∀ t : Fˣ, t ∈ Subgroup.zpowers k) ∧
      χ (principalTorusIn J k) ≠ 1 ∧
      (χ (principalTorusIn J k) : K)^2 + (χ (principalTorusIn J k) : K) + 1 = 0 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : CharP F 5 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hn := character_generator_ne_one J k hk χ hχ
  exact ⟨k, hk, hn, cubic_scalar_quadratic _ hn (borel_character_cube J hF χ _)⟩


universe v

/-- Apply a construction uniform in a generating torus parameter to every
original character of the fixed matrix model. The parameter is supplied here. -/
theorem model_filtrations_of_cubic_parameters
    (h : ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel modelForm →* Kˣ) (k : MatrixFieldˣ),
      (∀ t : MatrixFieldˣ, t ∈ Subgroup.zpowers k) →
      χ (principalTorusIn modelForm k) ≠ 1 →
      (χ (principalTorusIn modelForm k) : K)^2 +
        (χ (principalTorusIn modelForm k) : K) + 1 = 0 →
      FactorDegreeFiltration {21, 84}
        (ind (standardBorel modelForm).subtype (scalarCharacter χ))) : ModelFiltrations.{v} := by
  intro K _ _ _ χ hχ _
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hF : Nat.card MatrixField = 5 ^ 2 := GaloisField.card 5 2 (by decide)
  obtain ⟨k, hk, hn, hp⟩ := exists_cubic_parameter modelForm hF χ hχ
  exact h K χ k hk hn hp

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
