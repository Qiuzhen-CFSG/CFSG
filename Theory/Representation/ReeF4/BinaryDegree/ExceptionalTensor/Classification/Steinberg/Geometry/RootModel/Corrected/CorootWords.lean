module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Coroots
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# Literal coroot words for every F4 root

The regular cocharacter with negative integral simple-coroot coordinates equals
`n_r(t) n_r(1)⁻¹` in the concrete closed carrier. To prove this, transport both
signed root curves along one Tits word from a simple root. The same word
transports the diagonal matrix whose eigenvalue on the root vector for `q` is
`t ^ ⟨q, r⟩`; integral coroot expansion identifies this matrix with the published
cocharacter. This retains both the parameter and the root label for every root.

Composing with regular parameter inversion gives the raw convention. The
representation word remains `n_r(t) n_r(1)⁻¹`, while GLS uses the opposite product
`n_r(1)⁻¹ n_r(t)`. Source: GLS3, 1.9.6 and 1.12.1(e),(g),(i),
`refs/KGroup/GLS3/Chapter1.tex`, with the corrected inverse-parameter convention.
The matrix transport uses the integral Geck construction and the checked
characteristic-two simple-reflection formula.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def corootMatrix (r : F4Chevalley.Root) (t : Fˣ) :=
  F4Chevalley.torusElement (fun i => t ^ (-corootCoordinates r i))

omit [IsAlgClosed F] in
private lemma corootMatrix_weight (r : F4Chevalley.Root) (t : Fˣ)
    (a : F4Chevalley.BasisIndex) :
    F4Chevalley.basisTorusUnit (fun i => t ^ (-corootCoordinates r i)) a =
      t ^ chevalleyBasisWeight (P := typeF4RootPairing) a r := by
  rw [F4Chevalley.basisTorusUnit_formula]
  cases a with
  | inl i => simp [F4Chevalley.basisWeight, chevalleyBasisWeight]
  | inr q =>
    simp only [F4Chevalley.basisWeight, chevalleyBasisWeight, ← zpow_mul, neg_mul_neg]
    change (∏ i, t ^ (corootCoordinates r i * F4Chevalley.torusRootExponent q i)) = _
    rw [← corootCoordinates_pairing q r, Fin.sum_univ_four, Fin.prod_univ_four]
    simp only [zpow_add]

private lemma corootMatrix_simple (i : typeF4RootPairing_base.support) (t : Fˣ) :
    F4Chevalley.matrixH (F := F) i t = corootMatrix i t := by
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  rw [F4Chevalley.matrixH_simple]
  change _ = F4Chevalley.torusElement _
  rw [F4Chevalley.torusElement, ← F4Chevalley.torusParameter_simpleCoroot]
  congr 2
  funext q
  change t ^ F4Chevalley.simpleCorootExponent j q =
    t ^ (-corootCoordinates (typeF4SimpleRootIndex j) q)
  rw [corootCoordinates_simple]
  simp only [F4Chevalley.simpleCorootExponent]
  split_ifs <;> simp

omit [IsAlgClosed F] in
private lemma corootMatrix_word (w : List typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (t : Fˣ) :
    titsUnit w * corootMatrix r t =
      corootMatrix (reflectionWord (P := typeF4RootPairing) w r) t * titsUnit w := by
  apply Units.ext
  change specializeMatrix (titsWord w) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord w)
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change specializeMatrix (titsWord w) row col *
      (F4Chevalley.basisTorusUnit (k := F) _ col : F) =
    (F4Chevalley.basisTorusUnit (k := F) _ row : F) * specializeMatrix (titsWord w) row col
  rw [corootMatrix_weight, corootMatrix_weight]
  by_cases hz : titsWord (P := typeF4RootPairing) w row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsWord_respectsChevalleyGrading (P := typeF4RootPairing) w
      row col hz (reflectionWord (P := typeF4RootPairing) w r)
    rw [inverseReflectionWord_right_inverse] at hw
    rw [hw]
    exact mul_comm _ _

variable [CharP F 2]

omit [IsAlgClosed F] in
private lemma word_rootCurve (w : List typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (t : F) :
    titsUnit w * F4Chevalley.rootCurve r t * (titsUnit w)⁻¹ =
      F4Chevalley.rootCurve (reflectionWord (P := typeF4RootPairing) w r) t := by
  induction w with
  | nil => simp [reflectionWord]
  | cons i w ih =>
    have htw : titsUnit (S := F) (i :: w) = titsUnit [i] * titsUnit w := by
      rw [titsUnit_cons, titsUnit_cons, titsUnit_nil, mul_one]
    rw [htw]
    calc
      _ = titsUnit [i] * (titsUnit w * F4Chevalley.rootCurve r t *
          (titsUnit w)⁻¹) * (titsUnit [i])⁻¹ := by group
      _ = _ := by
        rw [ih]
        exact ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj i _ t

omit [IsAlgClosed F] in
private lemma word_matrixN (w : List typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (t : F) :
    titsUnit w * F4Chevalley.matrixN r t * (titsUnit w)⁻¹ =
      F4Chevalley.matrixN (reflectionWord (P := typeF4RootPairing) w r) t := by
  simp only [F4Chevalley.matrixN, ← reflectionWord_neg]
  rw [← word_rootCurve w r t, ← word_rootCurve w (-r) (-t⁻¹)]
  group

omit [IsAlgClosed F] in
private lemma word_matrixH (w : List typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (t : F) :
    titsUnit w * F4Chevalley.matrixH r t * (titsUnit w)⁻¹ =
      F4Chevalley.matrixH (reflectionWord (P := typeF4RootPairing) w r) t := by
  rw [F4Chevalley.matrixH, F4Chevalley.matrixH,
    ← word_matrixN w r t, ← word_matrixN w r (-1)]
  group

private lemma matrixH_all (r : F4Chevalley.Root) (t : Fˣ) :
    F4Chevalley.matrixH (F := F) r t = corootMatrix r t := by
  let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  rw [← D.target, ← word_matrixH, corootMatrix_simple, corootMatrix_word]
  group

omit [CharP F 2] in
private lemma corootWord_ambient (r : F4Chevalley.Root) (t : Fˣ) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (algebraicCorootElement r t) =
      F4Chevalley.matrixToAmbient (F4Chevalley.matrixH (F := F) r t) := by
  have hn (u : Fˣ) :
      (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
        (algebraicNElement r u) =
        F4Chevalley.matrixToAmbient (F4Chevalley.matrixN (F := F) r u) := by
    simp only [algebraicNElement, algebraicRootElement, map_mul,
      F4Chevalley.rootMorphism_inclusion_apply, F4Chevalley.matrixN,
      F4Chevalley.matrixToAmbient_root]
  rw [algebraicCorootElement, map_mul, map_inv, hn, hn, ← map_inv, ← map_mul]
  congr 1
  change _ = F4Chevalley.matrixN r (t : F) * F4Chevalley.matrixN r (-1)
  congr 1
  simp [F4Chevalley.matrixN, mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]

/-- Every representation cocharacter is the literal rank-one coroot word. -/
public theorem representationRootCocharacter_inclusion (r : F4Chevalley.Root)
    (t : Variety.Point (KMult F)) :
    letI := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
      ((representationRootCocharacter r).onPoints t) =
      algebraicCorootElement r (dPointEquiv 1 t 0) := by
  let _ := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  rw [representationRootCocharacter, F4Chevalley.splitTorusCocharacter_torusElement_apply,
    corootWord_ambient]
  change F4Chevalley.matrixToAmbient (corootMatrix r (dPointEquiv 1 t 0)) = _
  rw [matrixH_all]

/-- Every raw cocharacter is the literal coroot word at the inverse parameter. -/
public theorem rawRootCocharacter_inclusion (r : F4Chevalley.Root)
    (t : Variety.Point (KMult F)) :
    letI := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
      ((rawRootCocharacter r).onPoints t) =
      algebraicCorootElement r ((dPointEquiv 1 t 0)⁻¹) := by
  let _ := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
  rw [rawRootCocharacter_apply, representationRootCocharacter_inclusion, dPointEquiv_inv]
  rfl

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
