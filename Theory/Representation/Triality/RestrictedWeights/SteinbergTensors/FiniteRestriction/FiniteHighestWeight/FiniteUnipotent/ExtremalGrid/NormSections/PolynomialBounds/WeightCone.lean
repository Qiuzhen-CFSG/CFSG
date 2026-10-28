module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone.Roots
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone.RootActions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights

/-!
# Intrinsic weight cones for cyclic D4 highest-weight modules

For the actual positive Borel, every occurring character `mu` of a cyclic
rational highest-weight module satisfies `chi * mu⁻¹ = ∏ alpha_i ^ c_i`,
where `alpha_i` are the direct simple-root characters and `c_i` are natural
numbers. With an actual ambient point inverting the torus, the same assertion
holds for `chi * mu`. The opposite Borel uses `chi⁻¹` and `alpha_i⁻¹` in the
extremal specialization.

The proof first uses polynomial root-action coefficients to make the sum of
allowed weight spaces opposite-Borel invariant. A regular matrix coefficient
vanishing on the big cell vanishes everywhere; cyclicity therefore makes this
sum the entire module. Independence of weight spaces recovers the character
cone. The second equation uses the action of the supplied ambient inverter
on nonzero weight vectors, without an abstract Weyl representative assumption.

No irreducibility, dimension formula, finite evaluation, finite orbit spanning,
or chart support hypothesis occurs. The general statements allow any highest
character, and the extremal statements specialize to `(2^n - 1)rho`, including
`n = 1`. The inverter remains the explicit geometric input permitted by this
conditional helper's contract.

Sources: GLS3 §1.14; `refs/KGroup/GLS3/Chapter2St2.tex`, 13.2(d), 13.3(a);
Steinberg, *Representations of algebraic groups* (1963), §§2 and 8. The raw
inverse-conjugation characters are inverted at the left-action boundary, as
in the project's coroot convention audit.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
open Theory.AlgebraicGroup
open scoped BigOperators
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Every occurring weight of an actual cyclic highest-weight module lies
below the highest character in the positive simple-root cone. -/
theorem positive_weight_cone (S : Geometry K)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {chi : TorusWeight S.torus} {v : V}
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v chi)
    (hcyc : IsCyclicRepresentation rho v)
    (mu : TorusWeight S.torus) (hmu : mu ∈ representationWeights rho S.torus) :
    ∃ c : Fin 4 → ℕ, chi * mu⁻¹ = ∏ i, simpleCharacter S i ^ c i := by
  let M := characterCone (simpleCharacter S)
  have htop : lowerSpace rho S.torus M chi = ⊤ := by
    apply submodule_eq_top_of_dense_product rho hrho S.bigCell.data.B S.bigCell.data.Bopp
      (reverse_product_dense S.bigCell) v hv.1 hcyc
      (lowerSpace rho S.torus M chi) (highest_mem_lowerSpace rho M hv.2)
    intro g hg w hw
    exact lowerSpace_borel_stable S.roots S.realized rho hrho M chi
      S.bigCell.data.opposite_witness (negative_root_mem_cone S) S.rootParameter g hg hw
  exact weight_mem_of_lowerSpace_eq_top rho M chi mu htop hmu

/-- The opposite Borel uses the inverses of the direct positive simple-root
characters. Its highest character is left arbitrary. -/
theorem opposite_weight_cone (S : Geometry K)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {chi : TorusWeight S.torus} {v : V}
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v chi)
    (hcyc : IsCyclicRepresentation rho v)
    (mu : TorusWeight S.torus) (hmu : mu ∈ representationWeights rho S.torus) :
    ∃ c : Fin 4 → ℕ, chi * mu⁻¹ = ∏ i, (simpleCharacter S i)⁻¹ ^ c i := by
  let M := characterCone (fun i => (simpleCharacter S i)⁻¹)
  have htop : lowerSpace rho S.torus M chi = ⊤ := by
    apply submodule_eq_top_of_dense_product rho hrho S.bigCell.data.Bopp S.bigCell.data.B
      S.bigCell.product_dense v hv.1 hcyc
      (lowerSpace rho S.torus M chi) (highest_mem_lowerSpace rho M hv.2)
    intro g hg w hw
    exact lowerSpace_borel_stable S.roots S.realized rho hrho M chi
      S.bigCell.data.positive_witness (positive_root_mem_opposite_cone S) S.rootParameter g hg hw
  exact weight_mem_of_lowerSpace_eq_top rho M chi mu htop hmu

/-- An actual ambient inverter supplies the second positive cone inequality
inside the same representation. -/
theorem positive_weight_cone_of_inverter (S : Geometry K)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {chi : TorusWeight S.torus} {v : V}
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v chi)
    (hcyc : IsCyclicRepresentation rho v)
    (r : Variety.Point K) (hr : InvertsTorus S.torus r)
    (mu : TorusWeight S.torus) (hmu : mu ∈ representationWeights rho S.torus) :
    ∃ c : Fin 4 → ℕ, chi * mu = ∏ i, simpleCharacter S i ^ c i := by
  simpa only [inv_inv] using positive_weight_cone S rho hrho hv hcyc mu⁻¹
    (inverter_weight_occurs rho r hr hmu)

/-- The same ambient inverter supplies the second opposite cone inequality. -/
theorem opposite_weight_cone_of_inverter (S : Geometry K)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {chi : TorusWeight S.torus} {v : V}
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v chi)
    (hcyc : IsCyclicRepresentation rho v)
    (r : Variety.Point K) (hr : InvertsTorus S.torus r)
    (mu : TorusWeight S.torus) (hmu : mu ∈ representationWeights rho S.torus) :
    ∃ c : Fin 4 → ℕ, chi * mu = ∏ i, (simpleCharacter S i)⁻¹ ^ c i := by
  simpa only [inv_inv] using opposite_weight_cone S rho hrho hv hcyc mu⁻¹
    (inverter_weight_occurs rho r hr hmu)

/-- Both requested positive extremal character equations. The theorem includes
`n = 1` (and the trivial highest character at `n = 0`). -/
theorem positive_extremal_weight_cones (S : Geometry K) (n : ℕ)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {v : V}
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (hcyc : IsCyclicRepresentation rho v)
    (r : Variety.Point K) (hr : InvertsTorus S.torus r)
    (mu : TorusWeight S.torus) (hmu : mu ∈ representationWeights rho S.torus) :
    ∃ c d : Fin 4 → ℕ,
      S.leftWeightEmbedding (maximalRestrictedWeight n) * mu⁻¹ =
        ∏ i, ((S.roots.rootWeight (S.simpleRoot i).val)⁻¹) ^ c i ∧
      S.leftWeightEmbedding (maximalRestrictedWeight n) * mu =
        ∏ i, ((S.roots.rootWeight (S.simpleRoot i).val)⁻¹) ^ d i := by
  obtain ⟨c, hc⟩ := positive_weight_cone S rho hrho hv hcyc mu hmu
  obtain ⟨d, hd⟩ := positive_weight_cone_of_inverter S rho hrho hv hcyc r hr mu hmu
  exact ⟨c, d, hc, hd⟩

/-- Both requested opposite extremal equations, with highest character
`chi⁻¹` and simple characters `alpha_i⁻¹`. -/
theorem opposite_extremal_weight_cones (S : Geometry K) (n : ℕ)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {v : V}
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hcyc : IsCyclicRepresentation rho v)
    (r : Variety.Point K) (hr : InvertsTorus S.torus r)
    (mu : TorusWeight S.torus) (hmu : mu ∈ representationWeights rho S.torus) :
    ∃ c d : Fin 4 → ℕ,
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ * mu⁻¹ =
        ∏ i, (((S.roots.rootWeight (S.simpleRoot i).val)⁻¹)⁻¹) ^ c i ∧
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ * mu =
        ∏ i, (((S.roots.rootWeight (S.simpleRoot i).val)⁻¹)⁻¹) ^ d i := by
  obtain ⟨c, hc⟩ := opposite_weight_cone S rho hrho hv hcyc mu hmu
  obtain ⟨d, hd⟩ := opposite_weight_cone_of_inverter S rho hrho hv hcyc r hr mu hmu
  exact ⟨c, d, hc, hd⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
