module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Existence
public import Theory.AlgebraicGroup.RootSubgroups.Tangent

/-!
# The central D4 weight in the actual adjoint representation

The root `e₀ + e₁` pairs with the four simple coroots as `(0,1,0,0)`.
Its nonzero root tangent therefore has the positive central fundamental
left weight in the rational identity-tangent representation of the supplied
group. If the positive root groups centralize this root group, the tangent
is a highest vector for the unchanged Borel; the checked composition-factor
construction then supplies a rational irreducible.

The pointwise centralization premise is explicit and remains a geometric
obligation. This module proves the adjoint construction conditional on that
premise, not fundamental existence from `Geometry` alone. It uses no
characteristic-zero tangent integration or assumed irreducibility.

Sources: GLS3, Examples 1.14.9(c) and Theorem 1.14.6(d), with the direct
left-action convention of Steinberg (6.1), §13.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FundamentalModules
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The standard highest D4 root `e₀ + e₁`. -/
def highestRootIndex : TypeDRootIndex 4 :=
  ⟨⟨⟨0, 1⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

/-- The highest root is the central fundamental weight in coroot coordinates. -/
theorem highestRootIndex_pairing (i : Fin 4) :
    (typeDRootPairing 2).pairing highestRootIndex (typeDSimpleRootIndex 2 i) =
      ((Pi.single 1 1 : Fin 4 → ℝ) i) := by
  rw [typeDRootPairing_pairing]
  change (∑ j : Fin 4, _ * _) = _
  rw [Fin.sum_univ_four]
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  fin_cases i <;>
    norm_num [h20, h21, h30, h31, highestRootIndex, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, Pi.single_apply]

/-- The actual root index transported from the numbered D4 realization. -/
def highestRoot (S : Geometry K) : S.roots.Root := S.rootIndex.symm highestRootIndex

omit [IsAlgClosed k] in
/-- The highest root has coordinates `(0,1,0,0)` on the actual simple coroots. -/
theorem highestRoot_pairing (S : Geometry K) (i : Fin 4) :
    S.roots.pairing (highestRoot S) (S.simpleRoot i).val =
      (Pi.single 1 1 : Weight) i := by
  have h := S.based.1 (highestRoot S) (S.simpleRoot i).val
  rw [highestRoot, S.rootIndex.apply_symm_apply, S.simpleRoot_index,
    highestRootIndex_pairing] at h
  fin_cases i <;> norm_num [Pi.single_apply] at h ⊢ <;> exact_mod_cast h

omit [IsAlgClosed k] in
/-- The actual highest-root character is the raw central fundamental character. -/
theorem highestRoot_character (S : Geometry K) :
    S.roots.rootWeight (highestRoot S) = S.coordinateEmbedding (Pi.single 1 1) := by
  obtain ⟨a, ha⟩ := S.weight.surjective (S.roots.rootWeight (highestRoot S))
  have heq : a.toAdd = (Pi.single 1 1 : Weight) := by
    funext i
    rw [← S.weight_coordinate a.toAdd i]
    change S.roots.weightPairing (S.weight a) (S.simpleRoot i).val = _
    rw [ha, S.realized.weightPairing_rootWeight, highestRoot_pairing]
  rw [← ha]
  change S.weight a = S.weight (Multiplicative.ofAdd (Pi.single 1 1))
  exact congrArg S.weight (congrArg Multiplicative.ofAdd heq)

/-- The nonzero tangent obtained by differentiating the actual highest-root curve. -/
def highestRootVector (S : Geometry K) : IdentityPointDerivation K :=
  oneParameterTangent (S.roots.rootSubgroup (highestRoot S))
    (S.rootParameter (highestRoot S))

/-- In the direct adjoint action, this tangent has positive central left weight. -/
theorem highestRootVector_weight (S : Geometry K) :
    IsWeightVector (identityTangentRepresentation K) S.torus (highestRootVector S)
      (S.leftWeightEmbedding (Pi.single 1 1)) := by
  rw [S.leftWeightEmbedding_eq_inv, ← highestRoot_character]
  exact oneParameterTangent_isWeightVector S.torus _ _
    (S.realized.2.2.1 (highestRoot S)).2

/-- Pointwise centralization of the root curve fixes its tangent. -/
theorem highestRootVector_fixed_of_centralizes (S : Geometry K)
    (g : Variety.Point K)
    (hg : ∀ y, y ∈ S.roots.rootSubgroup (highestRoot S) → Commute g y) :
    ((identityTangentRepresentation K).action g).1 (highestRootVector S) =
      highestRootVector S := by
  apply Derivation.ext
  intro f
  rw [identityTangentRepresentation_action_apply]
  change kPlusIdentityDerivation
    (((S.roots.rootSubgroup (highestRoot S)).inclusion.comp
      (S.rootParameter (highestRoot S)).hom).toVariety.pullbackAlgHom
        ((Theory.AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f)) =
    kPlusIdentityDerivation
      (((S.roots.rootSubgroup (highestRoot S)).inclusion.comp
        (S.rootParameter (highestRoot S)).hom).toVariety.pullbackAlgHom f)
  congr 1
  apply Variety.PolynomialFunction.ext
  intro t
  change f (g * (S.roots.rootSubgroup (highestRoot S)).includePoint
    ((S.rootParameter (highestRoot S)).hom.onPoints t) * g⁻¹) = _
  have hy : (S.roots.rootSubgroup (highestRoot S)).includePoint
      ((S.rootParameter (highestRoot S)).hom.onPoints t) ∈
      S.roots.rootSubgroup (highestRoot S) :=
    ((S.roots.rootSubgroup (highestRoot S)).pointEquiv _).property
  rw [(hg _ hy).eq, mul_inv_cancel_right]
  rfl

/-- The remaining geometric input for the adjoint construction: each positive
root group centralizes the root group indexed by e₀ + e₁. -/
def PositiveCentralizesHighestRoot (S : Geometry K) : Prop :=
  ∀ r ∈ S.roots.positive, ∀ x, x ∈ S.roots.rootSubgroup r →
    ∀ y, y ∈ S.roots.rootSubgroup (highestRoot S) → Commute x y

/-- Centralization by the positive root groups makes this a highest vector. -/
theorem highestRootVector_highWeight (S : Geometry K)
    (hc : PositiveCentralizesHighestRoot S) :
    HasHighWeight (identityTangentRepresentation K) S.bigCell.data.B S.torus
      (highestRootVector S) (S.leftWeightEmbedding (Pi.single 1 1)) := by
  have hw := highestRootVector_weight S
  let H : Subgroup (Variety.Point K) := Subgroup.centralizer
    (S.roots.rootSubgroup (highestRoot S) : Set (Variety.Point K))
  have hle : RootSubgroupGenerated S.roots S.roots.positive ≤ H := by
    apply (Subgroup.closure_le H).2
    intro x hx
    obtain ⟨r, hr, hx⟩ := Set.mem_iUnion₂.mp hx
    intro y hy
    exact (hc r hr x hx y hy).symm.eq
  refine ⟨⟨hw.1, ?_⟩, hw⟩
  intro b hb
  obtain ⟨t, w, ht, hw', rfl⟩ := (S.bigCell.positive_decomposition b).mp hb
  let t' := S.torus.pointEquiv.symm ⟨t, ht⟩
  have ht' : S.torus.includePoint t' = t :=
    congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  refine ⟨(S.leftWeightEmbedding (Pi.single 1 1)).pointCharacter t', ?_⟩
  have hfix := highestRootVector_fixed_of_centralizes S w
    (fun y hy => (hle hw' y hy).symm)
  rw [map_mul, Units.val_mul, Module.End.mul_apply, hfix, ← ht']
  exact hw.2 t'

/-- Extract the central fundamental irreducible from the actual adjoint module. -/
theorem centralLeftRationalFactor_exists_of_centralizes (S : Geometry K)
    (hc : PositiveCentralizesHighestRoot S) :
    ∃ A : RationalFactor K, HasLeftHighestWeight S A (Pi.single 1 1) :=
  leftRationalFactor_exists_of_highWeight S (identityTangentRepresentation K)
    (identityTangentRepresentation_isRational K) (highestRootVector S)
    (highestRootVector_highWeight S hc)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FundamentalModules
