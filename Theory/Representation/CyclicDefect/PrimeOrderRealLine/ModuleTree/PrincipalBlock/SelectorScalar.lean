module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.Scalars

/-!
# The ordinary scalar of the literal congruence projector

The coefficient formula of `PrimeSelector` and ordinary orthogonality compute
the trace of the localized projector on each irreducible. Cancelling its
nonzero degree shows that its scalar is the indicator of the specified block.
No modular primitivity is used. Source: Feit III.8--9.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.PrimeBlockConstruction
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators
variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- The specified projector has the expected scalar on every ordinary row. -/
theorem localizedCentralScalar_selector (d : PrimeCongruenceBlockData p G)
    (b i : d.I) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec d.primeIdeal
      (d.chi i) (d.complete.1 i)
      ⟨PrimeSelector.localizedBlockElement d b,
        PrimeSelector.localizedBlockElement_mem_center d b⟩ =
      if i ∈ d.blockOf b then 1 else 0 := by
  classical
  let z : Subring.center (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
    ⟨PrimeSelector.localizedBlockElement d b,
      PrimeSelector.localizedBlockElement_mem_center d b⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  have hirr : Representation.IsIrreducible rho := by
    apply (irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [← hrho] using (d.complete.1 i).2
  let : Representation.IsIrreducible rho := hirr
  have hn : (n : ℂ) ≠ 0 := by
    have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := rho)
    have hpos : 0 < n := by
      simpa using ((Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance)
    exact_mod_cast hpos.ne'
  have hdegree : d.chi i (ConjClasses.mk (1 : G)) = (n : ℂ) := by
    rw [hrho]
    change rho.character 1 = (n : ℂ)
    simp [Representation.character]
  have hinner (j : d.I) :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        d.chi j (ConjClasses.mk g⁻¹) * d.chi i (ConjClasses.mk g) =
      if i = j then 1 else 0 := by
    have h := completeFamily_orthonormal d.complete i j
    rw [classFunctionInner] at h
    have hstar (g : G) : star (d.chi j (ConjClasses.mk g)) =
        d.chi j (ConjClasses.mk g⁻¹) := by
      rcases (d.complete.1 j).1 with ⟨m, sigma, hsigma⟩
      rw [hsigma]
      exact (Representation.representation_character_inv_eq_star_character sigma g).symm
    simpa only [hstar, mul_comm] using h
  have htrace := congrArg (LinearMap.trace ℂ (Fin n → ℂ))
    (localizedCentralScalar_action d i rho hrho z)
  rw [groupAlgebra_trace] at htrace
  simp only [map_smul, LinearMap.trace_one, Module.finrank_fin_fun, smul_eq_mul] at htrace
  have hchar (g : G) : rho.character g = d.chi i (ConjClasses.mk g) := by
    rw [hrho]; rfl
  simp only [MonoidAlgebra.coeff_mapRingHom, z, PrimeSelector.localizedBlockElement_coeff,
    hchar] at htrace
  have hsum :
      (∑ g : G, ((Nat.card G : ℂ)⁻¹ * ∑ j ∈ d.blockOf b,
        d.chi j (ConjClasses.mk 1) * d.chi j (ConjClasses.mk g⁻¹)) *
          d.chi i (ConjClasses.mk g)) =
      (if i ∈ d.blockOf b then (n : ℂ) else 0) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ j g, (Nat.card G : ℂ)⁻¹ *
        (d.chi j (ConjClasses.mk 1) * d.chi j (ConjClasses.mk g⁻¹)) *
          d.chi i (ConjClasses.mk g) =
        d.chi j (ConjClasses.mk 1) * ((Nat.card G : ℂ)⁻¹ *
          (d.chi j (ConjClasses.mk g⁻¹) * d.chi i (ConjClasses.mk g))) by
      intro j g; ring]
    simp_rw [← Finset.mul_sum, hinner]
    simp [hdegree]
  rw [hsum] at htrace
  apply PrimeIntegralModels.localizationToComplex_injective d.primeIdeal
  apply mul_right_cancel₀ hn
  by_cases hi : i ∈ d.blockOf b <;> simpa [z, hi] using htrace.symm

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
