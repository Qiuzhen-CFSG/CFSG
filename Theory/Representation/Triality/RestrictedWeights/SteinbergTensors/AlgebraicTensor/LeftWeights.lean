module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Geometry
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
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
open LeftWeights
universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]

/-- The source-correct embedding for left representations. -/
def D4Geometry.leftWeightEmbedding (S : D4Geometry K) : Weight ↪ TorusWeight S.torus :=
  LeftWeights.embedding S.characters

/-- Regular inversion on the actual torus. -/
def D4Geometry.torusInversion (S : D4Geometry K) :
    Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety :=
  inversion _ (isMulCommutative_iff.mp S.maximalTorus.1.isMulCommutative)

@[simp] theorem D4Geometry.torusInversion_apply (S : D4Geometry K)
    (t : Variety.Point S.torus.carrierVariety) : S.torusInversion.onPoints t = t⁻¹ := rfl

/-- The same simple coroot word at the inverse parameter. -/
def D4Geometry.leftSimpleCoroot (S : D4Geometry K) (i : Fin 4) :
    ClosedSubgroupTorusCocharacter S.torus := leftCocharacter (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i)))

theorem D4Geometry.leftWeightEmbedding_eq_raw (S : D4Geometry K) (a : Weight) :
    S.leftWeightEmbedding a = S.weightEmbedding (-a) := rfl

theorem D4Geometry.leftWeightEmbedding_eq_inv (S : D4Geometry K) (a : Weight) :
    S.leftWeightEmbedding a = (S.weightEmbedding a)⁻¹ := embedding_eq_inv S.characters a

theorem D4Geometry.leftWeightEmbedding_eq_pullback (S : D4Geometry K) (a : Weight) :
    S.leftWeightEmbedding a = TorusCharacter.pullback S.torusInversion (S.weightEmbedding a) := by
  rw [S.leftWeightEmbedding_eq_inv]
  exact (pullback_inversion _ _).symm

@[simp] theorem D4Geometry.leftWeightEmbedding_zero (S : D4Geometry K) :
    S.leftWeightEmbedding 0 = 1 := embedding_zero S.characters

@[simp] theorem D4Geometry.leftWeightEmbedding_neg (S : D4Geometry K) (a : Weight) :
    S.leftWeightEmbedding (-a) = (S.leftWeightEmbedding a)⁻¹ := embedding_neg S.characters a

theorem D4Geometry.leftWeightEmbedding_add (S : D4Geometry K) (a b : Weight) :
    S.leftWeightEmbedding (a + b) = S.leftWeightEmbedding a * S.leftWeightEmbedding b :=
  embedding_add S.characters a b

theorem D4Geometry.leftWeightEmbedding_zsmul (S : D4Geometry K) (m : ℤ) (a : Weight) :
    S.leftWeightEmbedding (m • a) = S.leftWeightEmbedding a ^ m := embedding_zsmul S.characters m a

theorem D4Geometry.leftWeightEmbedding_nsmul (S : D4Geometry K) (m : ℕ) (a : Weight) :
    S.leftWeightEmbedding (m • a) = S.leftWeightEmbedding a ^ m := embedding_nsmul S.characters m a

theorem D4Geometry.leftWeightEmbedding_sum (S : D4Geometry K) {ι : Type*}
    (s : Finset ι) (a : ι → Weight) :
    S.leftWeightEmbedding (∑ i ∈ s, a i) = ∏ i ∈ s, S.leftWeightEmbedding (a i) :=
  embedding_sum S.characters s a

/-- Evaluation on the raw coroot has the negative exponent. -/
theorem D4Geometry.leftWeightEmbedding_rawCoroot (S : D4Geometry K) (a : Weight) (i : Fin 4) :
    WeightCocharacterEquation S.torus (S.leftWeightEmbedding a)
      (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) (-a i) := by
  have h := S.realized.weightPairing_spec (S.weightEmbedding (-a)) (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))
  change WeightCocharacterEquation _ _ _
    (S.roots.weightPairing (S.characters (Multiplicative.ofAdd (-a))) (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) at h
  rw [S.coroot_coordinates] at h
  exact h

/-- Evaluation on the actual left simple coroot has the positive exponent. -/
theorem D4Geometry.leftWeightEmbedding_coroot (S : D4Geometry K) (a : Weight) (i : Fin 4) :
    WeightCocharacterEquation S.torus (S.leftWeightEmbedding a) (S.leftSimpleCoroot i) (a i) := by
  simpa only [D4Geometry.leftSimpleCoroot, neg_neg] using left_pairing (S.leftWeightEmbedding_rawCoroot a i)

/-- The normalizer itself is unchanged; its raw character equation is required. -/
theorem D4Geometry.leftWeightEmbedding_reflection (S : D4Geometry K)
    (c : Fin 4 → Variety.Point S.torus.carrierVariety → Variety.Point S.torus.carrierVariety)
    (hc : ∀ i a t, (S.weightEmbedding (reflection i a)).pointCharacter t =
      (S.weightEmbedding a).pointCharacter (c i t)) :
    ∀ i a t, (S.leftWeightEmbedding (reflection i a)).pointCharacter t =
      (S.leftWeightEmbedding a).pointCharacter (c i t) := reflection_character S.characters c hc

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
