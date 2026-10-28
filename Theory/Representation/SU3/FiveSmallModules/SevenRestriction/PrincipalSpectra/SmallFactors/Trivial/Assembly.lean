module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Inputs

/-!
# The spectral filtration of the literal trivial principal series

The constant line and the augmentation quotient carry the identity action,
so both have characteristic polynomial X − 1. The previously checked middle
quotients are simple of dimensions 104 and 20. Supplying the polynomial of
the literal upper quotient completes the four-factor spectral filtration.
The final equivalence uses the established inverse-coset convention for
Mathlib induction. The concrete upper polynomial is discharged in Trivial.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section


open Polynomial
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
open Degrees.TrivialCalculation
open Degrees.TrivialCalculation.MiddleFactors
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
universe v
section Ends
variable {K G Ω : Type*} [Field K] [Group G] [MulAction G Ω]

 theorem constants_action (x : G) :
    (constants (K := K) (G := G) (Ω := Ω)).toRepresentation x = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.property
  change functionAction x v.val = v.val
  rw [← ha]
  rfl

 theorem augmentation_quotient_action [Fintype Ω] (x : G) :
    (augmentationKernel (K := K) (G := G) (Ω := Ω)).quotientRepresentation x = 1 := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change Submodule.Quotient.mk (functionAction x v) = Submodule.Quotient.mk v
    apply (Submodule.Quotient.eq _).mpr
    change (∑ i, (functionAction x v - v) i) = 0
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    exact Equiv.sum_comp (MulAction.toPerm x⁻¹) v

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 theorem spectrum_of_trivial_line (ρ : Representation K G V) (x : G)
    (hd : Module.finrank K V = 1) (hx : ρ x = 1) :
    SmallSpectrum K (Module.finrank K V) (ρ x).charpoly := by
  intro _
  refine Or.inl ⟨hd, ?_⟩
  simp only [hx, LinearMap.charpoly_one, hd, pow_one, map_one]

 theorem filtration_of_trivial_line (ρ : Representation K G V) (x : G)
    (hd : Module.finrank K V = 1) (hx : ρ x = 1) :
    FactorPolynomialFiltration (SmallSpectrum K) x ρ := by
  have hq : Module.finrank K (V ⧸ (⊥ : Subrepresentation ρ).toSubmodule) = 1 := by
    change Module.finrank K (V ⧸ (⊥ : Submodule K V)) = 1
    rw [(Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
    exact hd
  have hqx : (⊥ : Subrepresentation ρ).quotientRepresentation x = 1 := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (ρ x v) = Submodule.Quotient.mk v
      rw [hx]
      rfl
  let : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
    inferInstanceAs (Subsingleton (⊥ : Submodule K V))
  exact .step ⊥ (.zero _) (irreducible_of_finrank_one _ hq)
    (spectrum_of_trivial_line _ x hq hqx)
end Ends

/-- The inversion convention for induction followed by coefficients on actual cosets. -/
noncomputable def inductionFunctionEquiv {K G : Type*} [Field K] [Group G]
    (B : Subgroup G) [Finite (G ⧸ B)] :
    (ind B.subtype (Degrees.scalarCharacter (1 : B →* Kˣ))).Equiv
      (functionAction (K := K) (G := G) (Ω := G ⧸ B)) :=
  .mk ((inductionCosetEquiv (K := K) B).trans (functionEquiv (K := K) (Ω := G ⧸ B))) (by
    intro g
    apply LinearMap.ext
    intro v
    exact (congrArg (functionEquiv (K := K) (Ω := G ⧸ B))
      (inductionCosetEquiv_equivariant B g v)).trans
      (functionEquiv_equivariant g (inductionCosetEquiv B v)))

variable {K : Type v} [Field K] [CharP K 2]

set_option backward.isDefEq.respectTransparency false in
theorem filtration_of_coordinates (c : Coordinates K) (x : CanonicalGroup)
    (hc : ((within c.space augmentationKernel).quotientRepresentation x).charpoly =
      sevenSpectrum K 20) :
    FactorPolynomialFiltration (SmallSpectrum K) x
      (functionAction (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints)) := by
  have hC : FactorPolynomialFiltration (SmallSpectrum K) x
      (constants (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints)).toRepresentation :=
    filtration_of_trivial_line _ x finrank_constants (constants_action x)
  let CU : Subrepresentation c.space.toRepresentation := within constants c.space
  have hCU : FactorPolynomialFiltration (V := CU.toSubmodule) (SmallSpectrum K) x CU.toRepresentation := by
    apply hC.transport (MonoidHom.id CanonicalGroup) (fun g => ⟨g, rfl⟩) _
      (withinEquiv constants c.space c.constants_le)
    intro g v
    rfl
  have hU : FactorPolynomialFiltration (SmallSpectrum K) x c.space.toRepresentation :=
    .step CU hCU (c.lower_irreducible binary_density_104) (by
      intro hd
      rw [c.lower_finrank] at hd
      omega)
  let UA : Subrepresentation (augmentationKernel (K := K) (G := CanonicalGroup)
      (Ω := CanonicalPoints)).toRepresentation := within c.space augmentationKernel
  have hUA : FactorPolynomialFiltration (V := UA.toSubmodule) (SmallSpectrum K) x UA.toRepresentation := by
    apply hU.transport (MonoidHom.id CanonicalGroup) (fun g => ⟨g, rfl⟩) _
      (withinEquiv c.space augmentationKernel c.le_augmentation)
    intro g v
    rfl
  have hA : FactorPolynomialFiltration (SmallSpectrum K) x
      (augmentationKernel (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints)).toRepresentation :=
    .step UA hUA (c.upper_irreducible binary_density_20) (by
      intro _
      exact Or.inr ⟨Or.inl c.upper_finrank, hc.trans (congrArg (sevenSpectrum K) c.upper_finrank.symm)⟩)
  exact .step augmentationKernel hA
    (irreducible_of_finrank_one _ finrank_augmentation_quotient)
    (spectrum_of_trivial_line _ x finrank_augmentation_quotient (augmentation_quotient_action x))

theorem induction_filtration_of_coordinates (c : Coordinates K) (x : CanonicalGroup)
    (hc : ((within c.space augmentationKernel).quotientRepresentation x).charpoly =
      sevenSpectrum K 20) :
    FactorPolynomialFiltration (SmallSpectrum K) x
      (ind canonicalBorel.subtype (Degrees.scalarCharacter (1 : canonicalBorel →* Kˣ))) := by
  let E := inductionFunctionEquiv (K := K) canonicalBorel
  apply (filtration_of_coordinates c x hc).transport (MonoidHom.id CanonicalGroup)
    (fun g => ⟨g, rfl⟩) _ E.symm.toLinearEquiv
  intro g v
  exact LinearMap.congr_fun (E.symm.isIntertwining' g) v
end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
