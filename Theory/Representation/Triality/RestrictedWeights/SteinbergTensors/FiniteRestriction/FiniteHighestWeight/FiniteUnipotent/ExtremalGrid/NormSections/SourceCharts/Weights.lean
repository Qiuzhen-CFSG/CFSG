module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.Resonance
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.WeylOrder

/-!
# Intrinsic simple-root bounds for actual chart words

A nonzero divided-power word is an occurring torus weight. The intrinsic
highest-weight cone, applied after an actual torus inverter, bounds its root
exponents by twice the extremal weight. The explicit D4 Cartan matrix converts
this character equality to the four inequalities defining RootWeightBound.
The opposite highest vector gives the identical inequalities with both character
orientations inverted. All calculations retain the supplied ordered roots.

Source: Steinberg (1963), Sections 2 and 8; GLS3 Chapter2St2, 13.2(d).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.SourceCharts
open DividedPowerEndpoint WeightCone
universe u v
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private def rootSums (d : Fin 12 →₀ ℕ) : Fin 4 → ℕ :=
  ![d 0+d 4+d 7+d 9+d 10+d 11,
    d 3+d 4+d 5+d 6+d 7+d 8+d 9+d 10+2*d 11,
    d 1+d 5+d 7+d 8+d 10+d 11,
    d 2+d 6+d 8+d 9+d 10+d 11]

private theorem rootSums_pairing (S : Geometry K) (d : Fin 12 →₀ ℕ) (j : Fin 4) :
    (∑ i : Fin 12, (d i : ℝ) * (rootWeight S (positiveCoordinateRoot S i) j : ℝ)) =
      ∑ a : Fin 4, (rootSums d a : ℝ) * (typeDCartanMatrix 2 a j : ℝ) := by
  simp only [positive_rootWeight_coordinate, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  fin_cases a <;>
    norm_num [rootSums,Triality.Standard.PositiveCoordinates.coefficients,Fin.sum_univ_succ,Fin.succ] <;> ring_nf <;> rfl

private theorem simple_weight_coordinate (S : Geometry K) (i j : Fin 4) :
    (rootWeight S (S.simpleRoot i).val j : ℝ) = (typeDCartanMatrix 2 i j : ℝ) := by
  have hi : positiveCoordinateRoot S (Triality.Standard.PositiveCoordinates.simplePosition i) =
      (S.simpleRoot i).val := by
    apply S.rootIndex.injective
    simp only [positiveCoordinateRoot, Equiv.apply_symm_apply,
      Triality.Standard.PositiveCoordinates.rootIndex_simple, S.simpleRoot_index]
  rw [← hi,positive_rootWeight_coordinate]
  fin_cases i <;>
    simp [Triality.Standard.PositiveCoordinates.coefficients,
      Triality.Standard.PositiveCoordinates.simplePosition,Fin.sum_univ_succ]

/-- Exact D4 character arithmetic gives the published four root-coordinate bounds. -/
theorem rootWeightBound_of_character_equation (S : Geometry K) (n : ℕ)
    (d : Fin 12 →₀ ℕ) (c : Fin 4 → ℕ)
    (he : S.leftWeightEmbedding (maximalRestrictedWeight n) ^ 2 =
      (∏ i, LeftWeights.leftRootCharacter S.roots (positiveCoordinateRoot S i) ^ d i) *
        ∏ i, simpleCharacter S i ^ c i) :
    PolynomialBounds.RootWeightBound (2^n) d := by
  have hw : 2 • maximalRestrictedWeight n =
      (∑ i : Fin 12, d i • rootWeight S (positiveCoordinateRoot S i)) +
        (∑ i : Fin 4, c i • rootWeight S (S.simpleRoot i).val) := by
    apply S.leftWeightEmbedding.injective
    simpa only [S.leftWeightEmbedding_add,S.leftWeightEmbedding_nsmul,
      S.leftWeightEmbedding_sum,rootWeight_character,LeftWeights.leftRootCharacter,
      simpleCharacter] using he
  have hq : 1 ≤ (2:ℕ)^n := Nat.one_le_pow n 2 (by decide)
  have hreal (j : Fin 4) :
      2 * ((2^n-1 : ℕ) : ℝ) =
        ∑ a : Fin 4, ((rootSums d a : ℝ)+(c a : ℝ)) * (typeDCartanMatrix 2 a j : ℝ) := by
    have hj := congrArg (fun w : D4RestrictedWeight.Weight => (w j : ℝ)) hw
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul,
      Pi.mul_apply, Pi.natCast_apply, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hj
    rw [rootSums_pairing] at hj
    simp only [simple_weight_coordinate] at hj
    rw [← Finset.sum_add_distrib] at hj
    simp only [← add_mul] at hj
    simpa only [maximalRestrictedWeight, Int.cast_sub, Int.cast_pow, Int.cast_ofNat,
      Int.cast_one, Nat.cast_sub hq, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hj
  have hm : typeDCartanMatrix 2 =
      !![(2:ℤ),-1,0,0; -1,2,-1,-1; 0,-1,2,0; 0,-1,0,2] := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [typeDCartanMatrix] <;> decide
  have h0 := hreal 0
  have h1 := hreal 1
  have h2 := hreal 2
  have h3 := hreal 3
  rw [hm] at h0 h1 h2 h3
  norm_num [Fin.sum_univ_succ,Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.succ, Nat.cast_sub hq] at h0 h1 h2 h3
  change 2*((2:ℝ)^n-1) = -(c 0:ℝ) - (rootSums d 0:ℝ) +
    (((rootSums d 1:ℝ)+(c 1:ℝ))*2 +
      (-(c 2:ℝ) - (rootSums d 2:ℝ) + (-(c 3:ℝ) - (rootSums d 3:ℝ)))) at h1
  change 2*((2:ℝ)^n-1) = -(c 1:ℝ) - (rootSums d 1:ℝ) +
    ((rootSums d 2:ℝ)+(c 2:ℝ))*2 at h2
  change 2*((2:ℝ)^n-1) = -(c 1:ℝ) - (rootSums d 1:ℝ) +
    ((rootSums d 3:ℝ)+(c 3:ℝ))*2 at h3
  have hc0 := Nat.cast_nonneg (α:=ℝ) (c 0)
  have hc1 := Nat.cast_nonneg (α:=ℝ) (c 1)
  have hc2 := Nat.cast_nonneg (α:=ℝ) (c 2)
  have hc3 := Nat.cast_nonneg (α:=ℝ) (c 3)
  have hb0 : (rootSums d 0 : ℝ) ≤ 6 * ((2^n-1:ℕ):ℝ) := by
    norm_num [Nat.cast_sub hq]
    linarith
  have hb1 : (rootSums d 1 : ℝ) ≤ 10 * ((2^n-1:ℕ):ℝ) := by
    norm_num [Nat.cast_sub hq]
    linarith
  have hb2 : (rootSums d 2 : ℝ) ≤ 6 * ((2^n-1:ℕ):ℝ) := by
    norm_num [Nat.cast_sub hq]
    linarith
  have hb3 : (rootSums d 3 : ℝ) ≤ 6 * ((2^n-1:ℕ):ℝ) := by
    norm_num [Nat.cast_sub hq]
    linarith
  have hb0' : rootSums d 0 ≤ 6 * (2^n-1) := by exact_mod_cast hb0
  have hb1' : rootSums d 1 ≤ 10 * (2^n-1) := by exact_mod_cast hb1
  have hb2' : rootSums d 2 ≤ 6 * (2^n-1) := by exact_mod_cast hb2
  have hb3' : rootSums d 3 ≤ 6 * (2^n-1) := by exact_mod_cast hb3
  exact ⟨hb0',hb1',hb2',hb3'⟩

variable [IsAlgClosed k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A nonzero negative-root word on the original positive highest vector
satisfies all four simple-root bounds, with no coefficient-support premise. -/
theorem negative_word_rootWeightBound (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (hcyc : IsCyclicRepresentation rho v)
    (r : K.Point) (hi : InvertsTorus S.torus r)
    (d : Fin 12 →₀ ℕ)
    (hne : (List.ofFn fun i => rootDividedPower S rho hr
      (negativeCoordinateRoot S i) (d i)).prod v ≠ 0) :
    PolynomialBounds.RootWeightBound (2^n) d := by
  let chi := S.leftWeightEmbedding (maximalRestrictedWeight n)
  let beta := ∏ i : Fin 12,
    LeftWeights.leftRootCharacter S.roots (positiveCoordinateRoot S i) ^ d i
  have hn (i : Fin 12) : LeftWeights.leftRootCharacter S.roots (negativeCoordinateRoot S i) =
      (LeftWeights.leftRootCharacter S.roots (positiveCoordinateRoot S i))⁻¹ :=
    congrArg Inv.inv (S.realized.2.2.2.1 _)
  have hw : (List.ofFn fun i => rootDividedPower S rho hr
      (negativeCoordinateRoot S i) (d i)).prod v ∈ weightSpace rho S.torus (chi * beta⁻¹) := by
    simpa only [List.map_ofFn,Function.comp_def,List.prod_ofFn,hn,inv_pow,
      Finset.prod_inv_distrib] using word_mem_weightSpace S rho hr
      (List.ofFn fun i => (negativeCoordinateRoot S i,d i)) hv.2.2
  have ho : chi * beta⁻¹ ∈ representationWeights rho S.torus :=
    (Submodule.ne_bot_iff _).mpr ⟨_,hw,hne⟩
  obtain ⟨c,hc⟩ := positive_weight_cone_of_inverter S rho hr hv hcyc r hi _ ho
  apply rootWeightBound_of_character_equation S n d c
  change chi^2 = beta * ∏ i, simpleCharacter S i ^ c i
  change chi * (chi * beta⁻¹) = _ at hc
  rw [← hc,mul_comm beta,pow_two]
  group

/-- The opposite highest vector gives the same root-coordinate inequalities
for the original ordered positive-root word. -/
theorem positive_word_rootWeightBound (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hcyc : IsCyclicRepresentation rho v)
    (r : K.Point) (hi : InvertsTorus S.torus r)
    (d : Fin 12 →₀ ℕ)
    (hne : (List.ofFn fun i => rootDividedPower S rho hr
      (positiveCoordinateRoot S i) (d i)).prod v ≠ 0) :
    PolynomialBounds.RootWeightBound (2^n) d := by
  let chi := S.leftWeightEmbedding (maximalRestrictedWeight n)
  let beta := ∏ i : Fin 12,
    LeftWeights.leftRootCharacter S.roots (positiveCoordinateRoot S i) ^ d i
  have hw : (List.ofFn fun i => rootDividedPower S rho hr
      (positiveCoordinateRoot S i) (d i)).prod v ∈ weightSpace rho S.torus (chi⁻¹ * beta) := by
    simpa only [List.map_ofFn,Function.comp_def,List.prod_ofFn] using word_mem_weightSpace S rho hr
      (List.ofFn fun i => (positiveCoordinateRoot S i,d i)) hv.2.2
  have ho : chi⁻¹ * beta ∈ representationWeights rho S.torus :=
    (Submodule.ne_bot_iff _).mpr ⟨_,hw,hne⟩
  obtain ⟨c,hc⟩ := opposite_weight_cone_of_inverter S rho hr hv hcyc r hi _ ho
  apply rootWeightBound_of_character_equation S n d c
  change chi^2 = beta * ∏ i, simpleCharacter S i ^ c i
  change chi⁻¹ * (chi⁻¹ * beta) = _ at hc
  calc
    chi^2 = beta * (chi⁻¹ * (chi⁻¹ * beta))⁻¹ := by group
    _ = _ := by rw [hc]; simp only [inv_pow, Finset.prod_inv_distrib, inv_inv]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.SourceCharts
