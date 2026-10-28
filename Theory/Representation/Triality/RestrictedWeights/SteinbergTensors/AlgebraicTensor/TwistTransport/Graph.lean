module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.HighestWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Orientation
public import Theory.AlgebraicGroup.Morphism.CodRestrict
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

/-!
# Forward and inverse graph twists of rational D4 factors

Restrict the pinned graph isomorphism to the actual torus variety. Its published
coroot formula determines the pullback character: the character-coordinate
isomorphism and uniqueness of integral Laurent exponents give composition with
the numbered vertex permutation. The inverse isomorphism gives the inverse
permutation. Borel stability transports highest vectors, and point surjectivity
preserves irreducibility. Opposite-Borel big-cell uniqueness yields actual linear
intertwiners with the corresponding basic factors in both directions.

Forward pullback uses `diagramAction`; inverse pullback uses
`inverseDiagramAction`. These are algebraic point-group equivalences and make
no assertion about irreducibility after finite restriction.

Source: GLS3, Definition 2.8.3 and Remarks 2.8.4 and 2.8.8,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- Restrict a torus-stabilizing morphism to the actual torus variety. -/
def torusRestriction (T : ClosedSubgroup K) (φ : Theory.AlgebraicGroup.Morphism K K)
    (hT : ∀ t, t ∈ T → φ.onPoints t ∈ T) :
    Theory.AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety :=
  (φ.comp T.inclusion).codRestrictClosedSubgroup T (fun t => hT _ (T.pointEquiv t).property)

omit [IsAlgClosed k] in
/-- Its inclusion agrees with the ambient group morphism. -/
theorem torusRestriction_include (T : ClosedSubgroup K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (hT : ∀ t, t ∈ T → φ.onPoints t ∈ T)
    (t : Variety.Point T.carrierVariety) :
    T.includePoint ((torusRestriction T φ hT).onPoints t) = φ.onPoints (T.includePoint t) :=
  Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _

/-- The coordinate isomorphism and Laurent-power uniqueness determine the
actual pullback character from the numbered coroot formula. -/
theorem pullback_character_of_coroots (S : D4Geometry K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (hT : ∀ t, t ∈ S.torus → φ.onPoints t ∈ S.torus)
    (π : Fin 4 → Fin 4)
    (hφ : ∀ i t,
      φ.onPoints (S.torus.includePoint
        ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t)) =
      S.torus.includePoint
        ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 (π i)))).onPoints t))
    (x : Weight) :
    TorusCharacter.pullback (torusRestriction S.torus φ hT) (S.weightEmbedding x) =
      S.weightEmbedding (x ∘ π) := by
  obtain ⟨y, hy⟩ := S.characters.surjective
    (TorusCharacter.pullback (torusRestriction S.torus φ hT) (S.weightEmbedding x))
  change S.weightEmbedding y.toAdd = _ at hy
  rw [← hy]
  congr 1
  funext i
  apply (weightCocharacterEquation_existsUnique S.torus (S.weightEmbedding y.toAdd)
    (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i)))).unique
    (S.weightEmbedding_coroot y.toAdd i)
  intro t
  rw [hy]
  change (S.weightEmbedding x).pointCharacter
    ((torusRestriction S.torus φ hT).onPoints
      ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t)) = _
  have ht : (torusRestriction S.torus φ hT).onPoints
      ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t) =
      (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 (π i)))).onPoints t := by
    apply S.torus.inclusion_injective
    exact (torusRestriction_include S.torus φ hT _).trans (hφ i t)
  rw [ht]
  exact S.weightEmbedding_coroot x (π i) t

/-- The forward graph pullback uses the forward numbered diagram permutation. -/
theorem PinnedTriality.pullback_character {S : D4Geometry K} (Γ : PinnedTriality S)
    (a : BasicWeight) :
    TorusCharacter.pullback (torusRestriction S.torus Γ.iso.hom Γ.torus_stable)
      (S.weightEmbedding (coefficient a)) = S.weightEmbedding (coefficient (diagramAction a)) := by
  exact pullback_character_of_coroots S Γ.iso.hom Γ.torus_stable
    typeD4DiagramPermutation Γ.coroot_formula (coefficient a)

omit [IsAlgClosed k] in
/-- The inverse graph map has the inverse numbered coroot formula. -/
theorem PinnedTriality.inverse_coroot_formula {S : D4Geometry K} (Γ : PinnedTriality S)
    (i : Fin 4) (t : Variety.Point (KMult k)) :
    Γ.iso.inv.onPoints (S.torus.includePoint
      ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t)) =
      S.torus.includePoint ((S.roots.rootCocharacter
        (S.rootEquiv.symm (typeDSimpleRootIndex 2 (typeD4DiagramPermutation.symm i)))).onPoints t) := by
  have h := Γ.coroot_formula (typeD4DiagramPermutation.symm i) t
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Γ.iso.hom_inv_id]

/-- Inverse graph pullback has exactly the inverse diagram weight. -/
theorem PinnedTriality.inverse_pullback_character {S : D4Geometry K} (Γ : PinnedTriality S)
    (a : BasicWeight) :
    TorusCharacter.pullback (torusRestriction S.torus Γ.iso.inv Γ.torus_inverse_stable)
      (S.weightEmbedding (coefficient a)) =
      S.weightEmbedding (coefficient (inverseDiagramAction a)) := by
  rw [inverseDiagramAction_eq_pullback]
  exact pullback_character_of_coroots S Γ.iso.inv Γ.torus_inverse_stable
    typeD4DiagramPermutation.symm Γ.inverse_coroot_formula (coefficient a)

omit [IsAlgClosed k] in
/-- Highest vectors pull back along a Borel- and torus-stabilizing morphism. -/
theorem pullback_hasHighWeight_character (B T : ClosedSubgroup K)
    (φ : Theory.AlgebraicGroup.Morphism K K)
    (hB : ∀ b, b ∈ B → φ.onPoints b ∈ B)
    (hT : ∀ t, t ∈ T → φ.onPoints t ∈ T)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (v : V) (χ : TorusWeight T)
    (hv : HasHighWeight ρ B T v χ) :
    HasHighWeight (pullback φ ρ) B T v
      (TorusCharacter.pullback (torusRestriction T φ hT) χ) := by
  refine ⟨⟨hv.1.1, fun b hb => hv.1.2 _ (hB b hb)⟩, hv.2.1, ?_⟩
  intro t
  change (ρ.action (φ.onPoints (T.includePoint t))).val v = _
  rw [← torusRestriction_include T φ hT, hv.2.2]
  rfl

/-- Forward graph pullback is linearly equivalent to the forward diagram factor. -/
theorem graphPullback_equivalent (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight) :
    ∃ e : (A.factor a).Space ≃ₗ[k] (A.factor (diagramAction a)).Space,
      Intertwines (pullback Γ.iso.hom (A.factor a).action)
        (A.factor (diagramAction a)).action e.toLinearMap := by
  obtain ⟨v, hv⟩ := A.highest a
  obtain ⟨w, hw⟩ := A.highest (diagramAction a)
  have ht := pullback_hasHighWeight_character S.borel S.torus Γ.iso.hom
    Γ.borel_stable Γ.torus_stable _ v _ hv
  rw [Γ.pullback_character] at ht
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell S.bigCell S.maximalTorus
    _ _ (pullback_irreducible Γ.iso.hom (fun g => ⟨Γ.iso.inv.onPoints g, Γ.iso.inv_hom_id g⟩)
      _ (A.factor a).irreducible) (A.factor (diagramAction a)).irreducible _ _ _ ht hw

/-- Inverse graph pullback is linearly equivalent to the inverse diagram factor. -/
theorem inverseGraphPullback_equivalent (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight) :
    ∃ e : (A.factor a).Space ≃ₗ[k] (A.factor (inverseDiagramAction a)).Space,
      Intertwines (pullback Γ.iso.inv (A.factor a).action)
        (A.factor (inverseDiagramAction a)).action e.toLinearMap := by
  obtain ⟨v, hv⟩ := A.highest a
  obtain ⟨w, hw⟩ := A.highest (inverseDiagramAction a)
  have ht := pullback_hasHighWeight_character S.borel S.torus Γ.iso.inv
    Γ.borel_inverse_stable Γ.torus_inverse_stable _ v _ hv
  rw [Γ.inverse_pullback_character] at ht
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell S.bigCell S.maximalTorus
    _ _ (pullback_irreducible Γ.iso.inv (fun g => ⟨Γ.iso.hom.onPoints g, Γ.iso.hom_inv_id g⟩)
      _ (A.factor a).irreducible) (A.factor (inverseDiagramAction a)).irreducible _ _ _ ht hw

/-- The actual point-representation equivalence for forward graph pullback. -/
def graphPullbackEquiv (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight) :
    Representation.Equiv ((A.factor a).restrict Γ.iso.hom.onPoints).ρ
      ((A.factor (diagramAction a)).restrict (MonoidHom.id _)).ρ :=
  .mk (graphPullback_equivalent S Γ A a).choose
    (fun g => LinearMap.ext ((graphPullback_equivalent S Γ A a).choose_spec g))

/-- The actual point-representation equivalence for inverse graph pullback. -/
def inverseGraphPullbackEquiv (S : D4Geometry K) (Γ : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight) :
    Representation.Equiv ((A.factor a).restrict Γ.iso.inv.onPoints).ρ
      ((A.factor (inverseDiagramAction a)).restrict (MonoidHom.id _)).ρ :=
  .mk (inverseGraphPullback_equivalent S Γ A a).choose
    (fun g => LinearMap.ext ((inverseGraphPullback_equivalent S Γ A a).choose_spec g))

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
