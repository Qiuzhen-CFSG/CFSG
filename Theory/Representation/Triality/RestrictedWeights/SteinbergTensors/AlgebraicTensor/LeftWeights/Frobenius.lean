module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Graph
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Pullback

/-!
# Frobenius and graph-field pullback of left weights

The published torus formula for OrdinaryFrobenius directly constructs its
restriction and proves the power formula for every iterate. Composing with the
pinned graph map preserves the forward/inverse permutation distinction.
Source: GLS3 2.8.3--4 and 2.8.8; Steinberg (6.1), §13.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]

private theorem maps_torus_of_power (T : ClosedSubgroup K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (r : ℕ)
    (hφ : ∀ t : Variety.Point T.carrierVariety,
      φ.onPoints (T.includePoint t) = T.includePoint (t ^ r)) :
    ∀ t, t ∈ T → φ.onPoints t ∈ T := by
  intro t ht
  let s := T.pointEquiv.symm ⟨t, ht⟩
  have hs : T.includePoint s = t :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  rw [← hs, hφ]
  exact (T.pointEquiv (s ^ r)).property

/-- Restrict the actual regular Frobenius iterate to the same torus. -/
def OrdinaryFrobenius.leftTorusMap {S : D4Geometry K} (F : OrdinaryFrobenius S) (n : ℕ) :
    Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety :=
  torusRestriction S.torus (iterate F.morphism n)
    (by exact maps_torus_of_power S.torus _ (2 ^ n) (F.iterate_torus n))

theorem OrdinaryFrobenius.leftTorusMap_apply {S : D4Geometry K}
    (F : OrdinaryFrobenius S) (n : ℕ) (t : Variety.Point S.torus.carrierVariety) :
    (F.leftTorusMap n).onPoints t = t ^ (2 ^ n) := by
  apply S.torus.inclusion_injective
  exact (torusRestriction_include _ _ _ t).trans (F.iterate_torus n t)

theorem OrdinaryFrobenius.pullback_leftWeight_iterate {S : D4Geometry K}
    (F : OrdinaryFrobenius S) (n : ℕ) (a : Weight) :
    TorusCharacter.pullback (F.leftTorusMap n) (S.leftWeightEmbedding a) =
      S.leftWeightEmbedding ((2 ^ n : ℕ) • a) :=
  LeftWeights.pullback_embedding_power S.characters _ _ (F.leftTorusMap_apply n) a

theorem OrdinaryFrobenius.pullback_leftWeight {S : D4Geometry K}
    (F : OrdinaryFrobenius S) (a : Weight) :
    TorusCharacter.pullback (F.leftTorusMap 1) (S.leftWeightEmbedding a) =
      S.leftWeightEmbedding ((2 : ℕ) • a) := by
  simpa only [pow_one] using F.pullback_leftWeight_iterate 1 a

variable [IsAlgClosed k]

/-- Forward graph after Frobenius: contravariance puts graph pullback first. -/
theorem graphField_pullback_leftWeight (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (Γ : PinnedTriality S) (n : ℕ) (a : Weight) :
    TorusCharacter.pullback
      ((torusRestriction S.torus Γ.iso.hom Γ.torus_stable).comp (F.leftTorusMap n))
      (S.leftWeightEmbedding a) =
        S.leftWeightEmbedding ((2 ^ n : ℕ) • (a ∘ typeD4DiagramPermutation)) := by
  change TorusCharacter.pullback (F.leftTorusMap n)
    (TorusCharacter.pullback (torusRestriction S.torus Γ.iso.hom Γ.torus_stable)
      (S.leftWeightEmbedding a)) = _
  rw [Γ.pullback_leftWeight, F.pullback_leftWeight_iterate]

theorem inverseGraphField_pullback_leftWeight (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (Γ : PinnedTriality S) (n : ℕ) (a : Weight) :
    TorusCharacter.pullback
      ((torusRestriction S.torus Γ.iso.inv Γ.torus_inverse_stable).comp (F.leftTorusMap n))
      (S.leftWeightEmbedding a) =
        S.leftWeightEmbedding ((2 ^ n : ℕ) • (a ∘ typeD4DiagramPermutation.symm)) := by
  change TorusCharacter.pullback (F.leftTorusMap n)
    (TorusCharacter.pullback (torusRestriction S.torus Γ.iso.inv Γ.torus_inverse_stable)
      (S.leftWeightEmbedding a)) = _
  rw [Γ.inverse_pullback_leftWeight, F.pullback_leftWeight_iterate]

omit [IsAlgClosed k] in
/-- Highest vectors of the actual iterate have the expected scaled left weight. -/
theorem leftPullback_hasHighWeight_iterate (S : D4Geometry K) (F : OrdinaryFrobenius S)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (v : V) (a : Weight)
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding a)) (n : ℕ) :
    HasHighWeight (pullback (iterate F.morphism n) ρ) S.borel S.torus v
      (S.leftWeightEmbedding ((2 ^ n : ℕ) • a)) := by
  rw [S.leftWeightEmbedding_nsmul]
  exact pullback_hasHighWeight_pow S.borel S.torus _ (2 ^ n)
    (F.iterate_borel n) (F.iterate_torus n) ρ v _ hv

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
