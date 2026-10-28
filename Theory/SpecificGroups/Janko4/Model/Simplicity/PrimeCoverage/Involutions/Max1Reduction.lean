module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Subgroup

/-!
# Reduction of involution coverage to the concrete ATLAS local subgroup

A subgroup of index prime to `p` contains a Sylow `p`-subgroup of the ambient
finite group. Thus conjugacy coverage inside it suffices for global coverage.
For the concrete `max1Subgroup`, the proposed orders give odd index 173067389.
It remains to prove its order and to fuse its involutions to the two specified
words; neither local claim is assumed as a fact in this module.

The subgroup words and proposed representatives are from the ATLAS J₄ entry
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ and the literal
`J4G1-max1W1` program documented in `Cardinality.Subgroup`.
-/

@[expose] public section

namespace Janko4.Simplicity

/-- Coverage inside a subgroup of index prime to `p` suffices. Conjugating
 elements are allowed to belong to the ambient group. -/
theorem prime_cyclic_coverage_of_subgroup_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {ι : Type*} (r : ι → G) (H : Subgroup G) (hindex : ¬p ∣ H.index)
    (hlocal : ∀ y : G, y ∈ H → orderOf y = p →
      ∃ i k g, r i = g * y ^ k * g⁻¹) : CoversPrime r p := by
  let P : Sylow p H := Sylow.nonempty.some
  let Q : Subgroup G := (P : Subgroup H).map H.subtype
  have hQ : ¬p ∣ Q.index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hindex
  let S : Sylow p G := (P.2.map H.subtype).toSylow hQ
  apply prime_cyclic_coverage_of_sylow r S
  intro y hy ho
  exact hlocal y (Subgroup.map_subtype_le (P : Subgroup H) hy) ho

/-- The exact local obligation: every involution in the specified matrix
subgroup is conjugate in the matrix carrier to one of the two proposed words. -/
def Max1InvolutionFusion
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) : Prop :=
  ∀ x : Model, x ∈ Cardinality.max1Subgroup hA hB → orderOf x = 2 →
    ∃ g : Model, a hA = g * x * g⁻¹ ∨
      word (a hA) (b hB) "ababb" ^ 5 = g * x * g⁻¹

/-- The proposed orders imply the exact odd index needed for transfer. -/
theorem max1_index_of_orders
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880)
    (hlocal : Nat.card (Cardinality.max1Subgroup hA hB) = 501397585920) :
    (Cardinality.max1Subgroup hA hB).index = 173067389 := by
  have hc := (Cardinality.max1Subgroup hA hB).card_mul_index
  rw [hcard, hlocal] at hc
  omega

/-- The two concrete local certificates finish the involution branch, given
 the model order. Indices 0 and 1 suffice, and no nontrivial power is needed
 inside the local subgroup. -/
theorem involution_coverage_of_max1_fusion
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880)
    (hlocal : Nat.card (Cardinality.max1Subgroup hA hB) = 501397585920)
    (hfusion : Max1InvolutionFusion hA hB) :
    CoversPrime (primeRepresentative (a hA) (b hB)) 2 := by
  have hindex : ¬2 ∣ (Cardinality.max1Subgroup hA hB).index := by
    rw [max1_index_of_orders hA hB hcard hlocal]
    decide
  apply prime_cyclic_coverage_of_subgroup_index _ _ hindex
  intro x hx ho
  obtain ⟨g, hg | hg⟩ := hfusion x hx ho
  · exact ⟨0, 1, g, by simpa only [primeRepresentative, Matrix.cons_val_zero, pow_one] using hg⟩
  · exact ⟨1, 1, g, by simpa only [primeRepresentative, Matrix.cons_val_one,
      Matrix.cons_val_zero, pow_one] using hg⟩

end Janko4.Simplicity
