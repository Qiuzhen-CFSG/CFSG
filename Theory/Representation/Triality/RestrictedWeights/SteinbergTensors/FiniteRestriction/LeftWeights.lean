module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Characters

/-!
# Left-action coordinates on the actual D4 torus

Keep the raw lattice, Borel and source coroot words. Precompose the character
isomorphism with negation and the coroots with regular inversion. Their pairing
is the original positive coordinate, as required by Steinberg (6.1) and §13,
in contrast to the inverse-conjugation convention of GLS3 §1.9 and 1.12.1.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open LeftWeights
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The source-correct embedding for left representations. -/
def Geometry.leftWeightEmbedding (S : Geometry K) : Weight ↪ TorusWeight S.torus :=
  LeftWeights.embedding S.weight

/-- Regular inversion on the actual torus. -/
def Geometry.torusInversion (S : Geometry K) :
    Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety :=
  inversion _ (isMulCommutative_iff.mp S.maximalTorus.1.isMulCommutative)

@[simp] theorem Geometry.torusInversion_apply (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) : S.torusInversion.onPoints t = t⁻¹ := rfl

/-- The same simple coroot word at the inverse parameter. -/
def Geometry.leftSimpleCoroot (S : Geometry K) (i : Fin 4) :
    ClosedSubgroupTorusCocharacter S.torus := leftCocharacter (S.roots.rootCocharacter (S.simpleRoot i).val)

theorem Geometry.leftWeightEmbedding_eq_raw (S : Geometry K) (a : Weight) :
    S.leftWeightEmbedding a = S.coordinateEmbedding (-a) := rfl

theorem Geometry.leftWeightEmbedding_eq_inv (S : Geometry K) (a : Weight) :
    S.leftWeightEmbedding a = (S.coordinateEmbedding a)⁻¹ := embedding_eq_inv S.weight a

theorem Geometry.leftWeightEmbedding_eq_pullback (S : Geometry K) (a : Weight) :
    S.leftWeightEmbedding a = TorusCharacter.pullback S.torusInversion (S.coordinateEmbedding a) := by
  rw [S.leftWeightEmbedding_eq_inv]
  exact (pullback_inversion _ _).symm

@[simp] theorem Geometry.leftWeightEmbedding_zero (S : Geometry K) :
    S.leftWeightEmbedding 0 = 1 := embedding_zero S.weight

@[simp] theorem Geometry.leftWeightEmbedding_neg (S : Geometry K) (a : Weight) :
    S.leftWeightEmbedding (-a) = (S.leftWeightEmbedding a)⁻¹ := embedding_neg S.weight a

theorem Geometry.leftWeightEmbedding_add (S : Geometry K) (a b : Weight) :
    S.leftWeightEmbedding (a + b) = S.leftWeightEmbedding a * S.leftWeightEmbedding b :=
  embedding_add S.weight a b

theorem Geometry.leftWeightEmbedding_zsmul (S : Geometry K) (m : ℤ) (a : Weight) :
    S.leftWeightEmbedding (m • a) = S.leftWeightEmbedding a ^ m := embedding_zsmul S.weight m a

theorem Geometry.leftWeightEmbedding_nsmul (S : Geometry K) (m : ℕ) (a : Weight) :
    S.leftWeightEmbedding (m • a) = S.leftWeightEmbedding a ^ m := embedding_nsmul S.weight m a

theorem Geometry.leftWeightEmbedding_sum (S : Geometry K) {ι : Type*}
    (s : Finset ι) (a : ι → Weight) :
    S.leftWeightEmbedding (∑ i ∈ s, a i) = ∏ i ∈ s, S.leftWeightEmbedding (a i) :=
  embedding_sum S.weight s a

/-- Evaluation on the raw coroot has the negative exponent. -/
theorem Geometry.leftWeightEmbedding_rawCoroot (S : Geometry K) (a : Weight) (i : Fin 4) :
    WeightCocharacterEquation S.torus (S.leftWeightEmbedding a)
      (S.roots.rootCocharacter (S.simpleRoot i).val) (-a i) := by
  have h := S.realized.weightPairing_spec (S.coordinateEmbedding (-a)) (S.simpleRoot i).val
  change WeightCocharacterEquation _ _ _
    (S.roots.weightPairing (S.weight (Multiplicative.ofAdd (-a))) (S.simpleRoot i).val) at h
  rw [S.weight_coordinate] at h
  exact h

/-- Evaluation on the actual left simple coroot has the positive exponent. -/
theorem Geometry.leftWeightEmbedding_coroot (S : Geometry K) (a : Weight) (i : Fin 4) :
    WeightCocharacterEquation S.torus (S.leftWeightEmbedding a) (S.leftSimpleCoroot i) (a i) := by
  simpa only [Geometry.leftSimpleCoroot, neg_neg] using left_pairing (S.leftWeightEmbedding_rawCoroot a i)

/-- The normalizer itself is unchanged; its raw character equation is required. -/
theorem Geometry.leftWeightEmbedding_reflection (S : Geometry K)
    (c : Fin 4 → Variety.Point S.torus.carrierVariety → Variety.Point S.torus.carrierVariety)
    (hc : ∀ i a t, (S.coordinateEmbedding (reflection i a)).pointCharacter t =
      (S.coordinateEmbedding a).pointCharacter (c i t)) :
    ∀ i a t, (S.leftWeightEmbedding (reflection i a)).pointCharacter t =
      (S.leftWeightEmbedding a).pointCharacter (c i t) := reflection_character S.weight c hc

variable [IsAlgClosed k]

/-- The restricted interval describes exponents on the actual left simple coroots. -/
theorem Geometry.leftRestrictedRange_iff (S : Geometry K) (n : ℕ) (a : Weight) :
    InRestrictedRange n a ↔ ∀ i, ∃ m : ℤ, 0 ≤ m ∧ m < (2 : ℤ) ^ n ∧
      WeightCocharacterEquation S.torus (S.leftWeightEmbedding a) (S.leftSimpleCoroot i) m := by
  constructor
  · intro ha i
    exact ⟨a i, (ha i).1, (ha i).2, S.leftWeightEmbedding_coroot a i⟩
  · intro h i
    obtain ⟨m, hm0, hmn, hm⟩ := h i
    have heq := (weightCocharacterEquation_existsUnique S.torus
      (S.leftWeightEmbedding a) (S.leftSimpleCoroot i)).unique
      (S.leftWeightEmbedding_coroot a i) hm
    exact heq.symm ▸ ⟨hm0, hmn⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
