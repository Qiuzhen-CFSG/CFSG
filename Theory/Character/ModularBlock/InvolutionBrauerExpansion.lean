module

public import Theory.Character.ModularBlock.TwoSectionContribution

/-!
# Integral Brauer expansions at central involutions

A central involution acts on each ordinary irreducible representation by `1`
or `-1`. Thus translating a character multiplies its integral multiplicities
and ordinary decomposition numbers by integral signs. This gives integral
coefficients in any supplied genuine principal Brauer family, without requiring
either the ordinary character or the Brauer characters to be real-valued.
The compatible local projection supplies the ambient two-section version.

Source: the central-scalar proof of generalized decomposition at an involution;
R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 373, (3.1).
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

namespace ModularBlock
open PrincipalBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- Central involutions have integral twisted decomposition coefficients even
when the Brauer family has nonreal values. -/
theorem TwistedBrauerExpansion.exists_int_of_sq_eq_one
    (d : PrincipalCongruenceBlockData G) {m : ℕ}
    (a : Cartan.PrincipalDecompositionData d m)
    (θ : ClassFunction G) (hθ : IsCharacter θ)
    (z : G) (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1)
    (hp : ∀ v : G, Odd (orderOf v) → θ (z * v) =
      ∑ i ∈ d.block, scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk (z * v))) :
    ∃ c : Fin m → ℤ,
      (∀ v : G, Odd (orderOf v) → θ (z * v) =
        ∑ j, (c j : ℂ) * BrauerCharacter.value d (a.family.rep j) v) ∧
      θ z = ∑ j, (c j : ℂ) * (a.family.degree j : ℂ) := by
  have hs (i : d.I) : ∃ k : ℤ, ∀ v,
      d.chi i (ConjClasses.mk (z * v)) = (k : ℂ) * d.chi i (ConjClasses.mk v) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    have hirr : Representation.IsIrreducible ρ := by
      apply (irreducible_iff_character_norm_one (ρ := ρ)).2
      simpa [← hρ] using (d.complete.1 i).2
    obtain ⟨s, hs, hpow⟩ := IsIrreducibleCharacter.exists_central_scalar
      (⟨n, ρ, hirr, rfl⟩ : IsIrreducibleCharacter ρ.character) hz
    have hi (v : G) : d.chi i (ConjClasses.mk v) = ρ.character v := by
      rw [hρ]
      rfl
    rcases sq_eq_one_iff.mp (hpow 2 hz2) with he | he
    · refine ⟨1, fun v => ?_⟩
      simpa only [hi, Int.cast_one, he] using hs v
    · refine ⟨-1, fun v => ?_⟩
      simpa only [hi, Int.cast_neg, Int.cast_one, he] using hs v
  choose sign hsign using hs
  have hm (i : d.I) : ∃ n : ℕ,
      scalarProduct G θ (fun g => d.chi i (ConjClasses.mk g)) = (n : ℂ) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    apply hθ.scalarProduct_nat
    exact ⟨n, ρ, by funext g; rw [hρ]; rfl⟩
  choose mult hmult using hm
  let c : Fin m → ℤ := fun j =>
    ∑ i ∈ d.block, (mult i : ℤ) * sign i * (a.decomposition i j : ℤ)
  have hc (j : Fin m) : (c j : ℂ) =
      ∑ i ∈ d.block, (mult i : ℂ) * (sign i : ℂ) * (a.decomposition i j : ℂ) := by
    simp [c]
  have he (v : G) (hv : Odd (orderOf v)) : θ (z * v) =
      ∑ j, (c j : ℂ) * BrauerCharacter.value d (a.family.rep j) v := by
    rw [hp v hv]
    calc
      _ = ∑ i ∈ d.block, ∑ j,
          ((mult i : ℂ) * (sign i : ℂ) * (a.decomposition i j : ℂ)) *
            BrauerCharacter.value d (a.family.rep j) v := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hmult, hsign, a.restriction i hi v hv, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [hc, Finset.sum_mul]
  exact ⟨c, he, by simpa using he 1 (by simp)⟩

/-- Actual integral generalized decomposition coefficients on an ambient
involution section, for an arbitrary principal-block character. -/
theorem TwoSectionContribution.exists_int_of_sq_eq_one
    (d : PrincipalCongruenceBlockData G)
    (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (y : G) (hy : y ^ 2 = 1) {m : ℕ}
    (a : Cartan.PrincipalDecompositionData
      (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({y} : Set G))) m) :
    ∃ c : Fin m → ℤ,
      (∀ v : Subgroup.centralizer ({y} : Set G), Odd (orderOf v) →
        χ (y * (v : G)) = ∑ j, (c j : ℂ) * BrauerCharacter.value
          (CompatibleBrauerBlock.localData d _) (a.family.rep j) v) ∧
      χ y = ∑ j, (c j : ℂ) * (a.family.degree j : ℂ) := by
  let C := Subgroup.centralizer ({y} : Set G)
  let z : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y)⟩
  have hz : z ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp v.property
  apply TwistedBrauerExpansion.exists_int_of_sq_eq_one _ a
    (fun g => χ (g : G)) (isCharacter_comp_hom C.subtype hχ) z hz (Subtype.ext hy)
  intro v hv
  obtain ⟨i, hi, hχi⟩ := hm
  simpa only [hχi, z, Subgroup.coe_mul] using
    TwoElementRestriction.principal_restriction_on_twoElement_section
      d y ⟨1, hy⟩ i hi v hv

end ModularBlock
