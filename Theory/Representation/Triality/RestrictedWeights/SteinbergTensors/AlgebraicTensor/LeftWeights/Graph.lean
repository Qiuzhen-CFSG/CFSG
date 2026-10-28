module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.TwistTransport.Graph

/-!
# Graph pullback in the corrected coordinates

The published pinned coroot equation directly discharges the character
comparison. Forward and inverse diagram permutations remain distinct. Borel
stability and highest-weight uniqueness give actual linear intertwiners.
Source: GLS3 2.8.3--4, 2.8.8, with Steinberg's convention (6.1).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- Transport the raw coroot pullback equation at the negative weight. -/
theorem pullback_leftCharacter_of_coroots (S : D4Geometry K)
    (φ : Theory.AlgebraicGroup.Morphism K K)
    (hT : ∀ t, t ∈ S.torus → φ.onPoints t ∈ S.torus) (π : Fin 4 → Fin 4)
    (hφ : ∀ i t, φ.onPoints (S.torus.includePoint
      ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t)) =
      S.torus.includePoint ((S.roots.rootCocharacter
        (S.rootEquiv.symm (typeDSimpleRootIndex 2 (π i)))).onPoints t)) (a : Weight) :
    TorusCharacter.pullback (torusRestriction S.torus φ hT) (S.leftWeightEmbedding a) =
      S.leftWeightEmbedding (a ∘ π) :=
  pullback_character_of_coroots S φ hT π hφ (-a)

theorem PinnedTriality.pullback_leftWeight {S : D4Geometry K} (Γ : PinnedTriality S)
    (a : Weight) :
    TorusCharacter.pullback (torusRestriction S.torus Γ.iso.hom Γ.torus_stable)
      (S.leftWeightEmbedding a) = S.leftWeightEmbedding (a ∘ typeD4DiagramPermutation) :=
  pullback_leftCharacter_of_coroots S Γ.iso.hom Γ.torus_stable _ Γ.coroot_formula a

theorem PinnedTriality.inverse_pullback_leftWeight {S : D4Geometry K} (Γ : PinnedTriality S)
    (a : Weight) :
    TorusCharacter.pullback (torusRestriction S.torus Γ.iso.inv Γ.torus_inverse_stable)
      (S.leftWeightEmbedding a) = S.leftWeightEmbedding (a ∘ typeD4DiagramPermutation.symm) :=
  pullback_leftCharacter_of_coroots S Γ.iso.inv Γ.torus_inverse_stable _ Γ.inverse_coroot_formula a

theorem PinnedTriality.pullback_leftCharacter {S : D4Geometry K} (Γ : PinnedTriality S)
    (a : BasicWeight) :
    TorusCharacter.pullback (torusRestriction S.torus Γ.iso.hom Γ.torus_stable)
      (S.leftWeightEmbedding (coefficient a)) =
      S.leftWeightEmbedding (coefficient (diagramAction a)) := Γ.pullback_leftWeight _

theorem PinnedTriality.inverse_pullback_leftCharacter {S : D4Geometry K} (Γ : PinnedTriality S)
    (a : BasicWeight) :
    TorusCharacter.pullback (torusRestriction S.torus Γ.iso.inv Γ.torus_inverse_stable)
      (S.leftWeightEmbedding (coefficient a)) =
      S.leftWeightEmbedding (coefficient (inverseDiagramAction a)) := by
  rw [inverseDiagramAction_eq_pullback]
  exact Γ.inverse_pullback_leftWeight _

/-- Forward graph pullback is linearly equivalent to the forward diagram factor. -/
theorem leftGraphPullback_equivalent (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight) :
    ∃ e : (A.factor a).Space ≃ₗ[k] (A.factor (diagramAction a)).Space,
      Intertwines (pullback Γ.iso.hom (A.factor a).action)
        (A.factor (diagramAction a)).action e.toLinearMap := by
  obtain ⟨v, hv⟩ := A.highest a
  obtain ⟨w, hw⟩ := A.highest (diagramAction a)
  have ht := pullback_hasHighWeight_character S.borel S.torus Γ.iso.hom
    Γ.borel_stable Γ.torus_stable _ v _ hv
  rw [Γ.pullback_leftCharacter] at ht
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell S.bigCell S.maximalTorus
    _ _ (pullback_irreducible Γ.iso.hom (fun g => ⟨Γ.iso.inv.onPoints g, Γ.iso.inv_hom_id g⟩)
      _ (A.factor a).irreducible) (A.factor (diagramAction a)).irreducible _ _ _ ht hw

/-- Inverse graph pullback is linearly equivalent to the inverse diagram factor. -/
theorem leftInverseGraphPullback_equivalent (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight) :
    ∃ e : (A.factor a).Space ≃ₗ[k] (A.factor (inverseDiagramAction a)).Space,
      Intertwines (pullback Γ.iso.inv (A.factor a).action)
        (A.factor (inverseDiagramAction a)).action e.toLinearMap := by
  obtain ⟨v, hv⟩ := A.highest a
  obtain ⟨w, hw⟩ := A.highest (inverseDiagramAction a)
  have ht := pullback_hasHighWeight_character S.borel S.torus Γ.iso.inv
    Γ.borel_inverse_stable Γ.torus_inverse_stable _ v _ hv
  rw [Γ.inverse_pullback_leftCharacter] at ht
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell S.bigCell S.maximalTorus
    _ _ (pullback_irreducible Γ.iso.inv (fun g => ⟨Γ.iso.hom.onPoints g, Γ.iso.hom_inv_id g⟩)
      _ (A.factor a).irreducible) (A.factor (inverseDiagramAction a)).irreducible _ _ _ ht hw

/-- The actual point-representation equivalence for forward graph pullback. -/
def leftGraphPullbackEquiv (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight) :
    Representation.Equiv ((A.factor a).restrict Γ.iso.hom.onPoints).ρ
      ((A.factor (diagramAction a)).restrict (MonoidHom.id _)).ρ :=
  .mk (leftGraphPullback_equivalent S Γ A a).choose
    (fun g => LinearMap.ext ((leftGraphPullback_equivalent S Γ A a).choose_spec g))

/-- The actual point-representation equivalence for inverse graph pullback. -/
def leftInverseGraphPullbackEquiv (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight) :
    Representation.Equiv ((A.factor a).restrict Γ.iso.inv.onPoints).ρ
      ((A.factor (inverseDiagramAction a)).restrict (MonoidHom.id _)).ρ :=
  .mk (leftInverseGraphPullback_equivalent S Γ A a).choose
    (fun g => LinearMap.ext ((leftInverseGraphPullback_equivalent S Γ A a).choose_spec g))

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
