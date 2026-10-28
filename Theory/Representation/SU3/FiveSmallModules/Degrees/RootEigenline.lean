module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Contracts
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.RationalLine
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Geometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity

/-!
# Borel eigenlines from root-restriction calculations in SU₃(5)

Write the degree as z + 20a, where z is the dimension fixed by the root
center and a is positive. In degrees 22–24, necessarily a=1 and 2≤z≤4.
Nontrivial linear root characters occur in torus orbits of size eight, so
the entire center-fixed space is root fixed. The torus preserves that space
and has projective order eight.
Absolute irreducibility makes central torus powers scalar, and the scalar
has an eighth root in the original finite field. The resulting nilpotent
operator has a nonzero kernel, giving a rational Borel eigenline.

The unconditional `root_eigenline_input` combines the proved nonlinear
multiplicity and dual-character gap with this rational-line construction.
No splitting-field hypothesis or faithfulness on SU₃ is used.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
p.10; Aschbacher–Smith K.2, printed p.453.
-/

public section
open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees

universe u v
open RootEigenline

/-- The canonical torus gives a rational Borel line in any nonzero root-fixed
space of an absolutely irreducible representation. -/
theorem borel_eigenline_of_root_fixed_space
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U) (hi : τ.IsAbsolutelyIrreducible)
    (hfixed : Representation.invariants (τ.comp (standardRoot J).subtype) ≠ ⊥) :
    ∃ (χ : standardBorel J →* Kˣ) (v : U),
      v ≠ 0 ∧ ∀ b : standardBorel J, τ b v = (χ b : K) • v := by
  let : τ.IsAbsolutelyIrreducible := hi
  let T := specialTorus (FormTransport.standardForm J) rfl
  let : IsCyclic T := (specialEquiv (FormTransport.standardForm J) rfl).isCyclic.mp
    inferInstance
  exact eigenline_of_fixed_space τ (standardRoot J) T
    (specialTorus_normalizes_root (FormTransport.standardForm J) rfl)
    (specialTorus_eighth_power_central (FormTransport.standardForm J) rfl hc hconj)
    hfixed

/-- The nonlinear multiplicity and linear-character gap force root-fixed
dimension 2–4 in the excluded window. -/
theorem root_fixed_dimension_of_root_calculations
    (hnonlinear : RootNonlinearMultiplicityInput.{u, v})
    (hlinear : RootLinearGapInput.{u, v})
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hk : τ.ker ≤ Subgroup.center (standardGroup J))
    (hlo : 22 ≤ Module.finrank K U) (hhi : Module.finrank K U ≤ 24) :
    2 ≤ Module.finrank K (Representation.invariants (τ.comp (standardRoot J).subtype)) ∧
      Module.finrank K (Representation.invariants (τ.comp (standardRoot J).subtype)) ≤ 4 := by
  obtain ⟨a, ha, hda⟩ := hnonlinear F J hc hconj K U τ hk
  have hz : Module.finrank K (Representation.invariants
      (τ.comp (standardRootCenter J).subtype)) < 8 := by omega
  rw [hlinear F J hc hconj K U τ hz]
  omega

/-- Assembly with two independent root-restriction inputs. -/
theorem root_eigenline_input_of_root_calculations
    (hnonlinear : RootNonlinearMultiplicityInput.{u, v})
    (hlinear : RootLinearGapInput.{u, v}) : RootEigenlineInput.{u, v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ τ hk hi hlo hhi
  have hd := root_fixed_dimension_of_root_calculations hnonlinear hlinear J hc hconj τ hk hlo hhi
  apply borel_eigenline_of_root_fixed_space J hc hconj τ hi
  intro hz
  rw [hz, finrank_bot] at hd
  omega

/-- Every absolutely irreducible characteristic-two representation of the
literal SU₃(5) with central kernel and degree 22–24 has a Borel eigenline over
its original finite coefficient field. Both root-restriction inputs are
discharged by the canonical root calculations. -/
theorem root_eigenline_input : RootEigenlineInput.{u, v} :=
  root_eigenline_input_of_root_calculations
    root_nonlinear_multiplicity_input root_linear_gap_input

end Representation.SU3.FiveSmallModules.Degrees
