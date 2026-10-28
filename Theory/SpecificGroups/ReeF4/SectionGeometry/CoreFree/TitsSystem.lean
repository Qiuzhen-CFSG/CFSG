module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientCalculations
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.LinearParabolic
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.NormalizerWords
public import Theory.AlgebraicGroup.BNPair.MaximalParabolic

/-!
# The concrete Ree Tits system and its linear parabolic

The Borel is the fixed root Borel and the normalizer is the fixed subgroup of
all nonzero split rank-one words. The quotient reductions construct the
BN-pair from normality of their intersection, generation of the normalizer
by its torus and two orbit words, and the concrete exchange and nontriviality
calculations. The already proved linear-parabolic generation identity then
identifies its standard parabolic. Its retained word is `[0,3]`, so its omitted
relative reflection is the Suzuki word `[1,2,1,2]`.

The Weyl-monomial presentation and triangular torus kernel of the split
normalizer words discharge the geometric premises, using the proved equality
of the coroot and diagonal tori. This constructs `titsSystem m` on the full
exceptional fixed group `Model m`, including the binary endpoint, without
simplicity or residual identification. For `1 ≤ m`, `exists_titsSystem`
identifies the root-defined linear parabolic with the standard parabolic
omitting the Suzuki reflection.

Source: GLS3 Theorems 2.3.4(b), 2.3.5 and 2.6.5, Definition 2.6.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Subgroup LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open scoped Pointwise

section WordCalculations

variable (m : ℕ)
variable [hNormal : ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)).Normal]
variable (hN : normalizerWords m ≤ fixedTorus m ⊔ weylSubgroup m)
variable (hex : ∀ s : Side, ∀ n ∈ normalizerWords m, ∀ b ∈ borel m,
  weylLift m s * b * n ∈ borelCell m (weylLift m s * n) ∪ borelCell m n)
variable (hw : ∀ s : Side, ∃ b ∈ borel m,
  weylLift m s * b * weylLift m s ∉ borel m)

/-- Conditional construction on the specified concrete Borel and normalizer. -/
def titsSystemOfWordCalculations : TitsSystem (X := Model m) where
  B := borel m
  N := normalizerWords m
  generate := borel_normalizerWords_generate m
  intersection_normal := inferInstance
  S := simpleReflections m
  finite_S := simpleReflections_finite m
  involutions := by
    rintro _ ⟨s, rfl⟩
    exact ⟨simpleReflection_ne_one_of_witness m s (hw s), simpleReflection_sq m s⟩
  quotient_generate := simpleReflections_generate_of_normalizerWords m hN
  exchange := exchange_of_word_exchange m hex
  nontrivial := nontrivial_of_word_witness m hw

/-- The end-node parabolic omits the middle-node relative reflection. -/
theorem titsSystemOfWordCalculations_linearParabolic (hm : 1 ≤ m)
    (hsep : (weylLift m .linear)⁻¹ * weylLift m .suzuki ∉ borel m) :
    (titsSystemOfWordCalculations m hN hex hw).standardParabolic
      ((titsSystemOfWordCalculations m hN hex hw).S \ {simpleReflection m .suzuki}) =
        parabolic m .linear := by
  let T := titsSystemOfWordCalculations m hN hex hw
  change T.standardParabolic (simpleReflections m \ {simpleReflection m .suzuki}) = _
  refine (congrArg T.standardParabolic (simpleReflections_sdiff_suzuki m
    (simpleReflection_linear_ne_suzuki_of_separation m hsep))).trans ?_
  have hcell : weylLift m .linear ∈ T.bruhatCell (simpleReflection m .linear) :=
    T.representative_mem_bruhatCell _ (simpleLift m .linear) rfl
  apply le_antisymm
  · apply T.standardParabolic_le (parabolic m .linear) (borel_le_parabolic m .linear)
    rintro s hs
    have hs' : s = simpleReflection m .linear := hs
    subst s
    exact T.bruhatCell_subset_of_mem (parabolic m .linear) (borel_le_parabolic m .linear)
      hcell (seed_le_parabolic m .linear (weylLift_mem_seed m .linear))
  · rw [linear_parabolic_eq_borel_sup_weyl m hm]
    exact sup_le (T.B_le_standardParabolic _)
      (zpowers_le.mpr (T.bruhatCell_subset_standardParabolic_of_mem
        (Set.mem_singleton _) hcell))

include hNormal hN hex hw in
/-- Assembly retains every remaining word calculation as an explicit premise.
It is not the unconditional Ree Tits-system existence theorem. -/
theorem exists_titsSystem_of_word_calculations (hm : 1 ≤ m)
    (hsep : (weylLift m .linear)⁻¹ * weylLift m .suzuki ∉ borel m) :
    ∃ T : TitsSystem (X := Model m), T.B = borel m ∧
      ∃ s ∈ T.S, T.standardParabolic (T.S \ {s}) = parabolic m .linear := by
  refine ⟨titsSystemOfWordCalculations m hN hex hw, rfl,
    simpleReflection m .suzuki, simpleReflection_mem m .suzuki, ?_⟩
  exact titsSystemOfWordCalculations_linearParabolic m hN hex hw hm hsep

end WordCalculations

/-- The fixed torus is normal inside the concrete normalizer-word subgroup. -/
theorem borel_inf_normalizerWords_normal (m : ℕ) :
    ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)).Normal :=
  borel_inf_normalizerWords_normal_of_kernel m (fun _ hn =>
    Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn)

attribute [local instance] borel_inf_normalizerWords_normal

/-- Every fixed normalizer word is generated by the full fixed torus and the
two actual relative simple lifts. -/
theorem normalizerWords_le_fixedTorus_sup_weylSubgroup (m : ℕ) :
    normalizerWords m ≤ fixedTorus m ⊔ weylSubgroup m :=
  normalizerWords_le_fixedTorus_sup_weylSubgroup_of_monomial m
    (fun _ hn => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) hn)
    (fun _ hn => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn)

/-- Relative exchange for the concrete Borel and normalizer, with all matrix
premises discharged. -/
theorem word_exchange (m : ℕ) :
    ∀ s : Side, ∀ n ∈ normalizerWords m, ∀ b ∈ borel m,
      weylLift m s * b * n ∈ borelCell m (weylLift m s * n) ∪ borelCell m n :=
  word_exchange_of_monomial m
    (fun _ hn => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) hn)
    (fun _ hn => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn)

/-- The BN-pair on the full exceptional fixed group, with the root-defined
Borel, the fixed normalizer words, and the two relative simple reflections. -/
def titsSystem (m : ℕ) : TitsSystem (X := Model m) :=
  titsSystemOfWordCalculations m (normalizerWords_le_fixedTorus_sup_weylSubgroup m)
    (word_exchange m) (weylLift_borel_conjugation_witness m)

@[simp] theorem titsSystem_B (m : ℕ) : (titsSystem m).B = borel m := rfl

@[simp] theorem titsSystem_N (m : ℕ) : (titsSystem m).N = normalizerWords m := rfl

@[simp] theorem titsSystem_S (m : ℕ) : (titsSystem m).S = simpleReflections m := rfl

/-- The end-node linear parabolic retains `[0,3]` and omits the relative
Suzuki reflection `[1,2,1,2]`. -/
theorem titsSystem_linearParabolic (m : ℕ) (hm : 1 ≤ m) :
    (titsSystem m).standardParabolic
      ((titsSystem m).S \ {simpleReflection m .suzuki}) = parabolic m .linear :=
  titsSystemOfWordCalculations_linearParabolic m
    (normalizerWords_le_fixedTorus_sup_weylSubgroup m) (word_exchange m)
    (weylLift_borel_conjugation_witness m) hm
    (weylLift_linear_inv_mul_suzuki_not_mem_borel m)

/-- Unconditional Ree BN-pair existence and comparison with the root-defined
linear parabolic, on the full fixed group for every field size at least eight. -/
theorem exists_titsSystem (m : ℕ) (hm : 1 ≤ m) :
    ∃ T : TitsSystem (X := Model m), T.B = borel m ∧
      ∃ s ∈ T.S, T.standardParabolic (T.S \ {s}) = parabolic m .linear := by
  exact ⟨titsSystem m, titsSystem_B m, simpleReflection m .suzuki,
    simpleReflection_mem m .suzuki, titsSystem_linearParabolic m hm⟩

end ReeF4.SectionGeometry.BNPair
