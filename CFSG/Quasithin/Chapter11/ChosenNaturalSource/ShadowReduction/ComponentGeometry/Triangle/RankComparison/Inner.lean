module
public import Theory.Representation.G2NaturalNormalizerOffenders
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.ElementaryAbelian.Injective

/-!
# Removing outer actors from the small moved-space comparison

A nontrivial field involution in the full binary natural G₂(4) normalizer
moves six dimensions. Thus an elementary actor whose entire moved space has
dimension at most four has trivial field part. The scalar factor of each
involution is then one, so the actor lies in the actual inner image. Its
preimage retains the literal moved space and image rank.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776; the normalizer and
involution calculations use B.4.6, printed pp.88--90.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
attribute [local instance] ZMod.algebra
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- Four-dimensional movement excludes the outer field part of an elementary actor. -/
theorem small_moved_le_inner (hF : Nat.card F = 4)
    (B : Subgroup (linearNormalizer (Natural.Normalizer.binary F)))
    [IsElementaryAbelian 2 B]
    (hm : Module.finrank (ZMod 2)
      (subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B) ≤ 4) :
    B ≤ (normalizerEmbedding (Natural.Normalizer.binary F)).range := by
  intro t ht
  have hq : 2 < Nat.card F := by omega
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  obtain ⟨z,hz⟩ := LieAutomorphismExtensions.semilinearAction_surjective hq
    (Natural.Normalizer.normalizerAutomorphism F t)
  by_cases hs : z.right = 1
  · exact Natural.Normalizer.inner_involution_mem F hq t ht2 z hz hs
  have hd := Natural.Normalizer.field_involution_codim F hq
    (show Nat.card F = 2 ^ 2 by omega) t ht2 z hz hs
  rw [fixedCodim_zpowers_eq_displacement_rank] at hd
  have hle : LinearMap.range (normalizerRepresentation (Natural.Normalizer.binary F) t - LinearMap.id) ≤
      subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨t,ht,v,Submodule.mem_top,rfl⟩
  have hdim := Submodule.finrank_mono hle
  omega

/-- The inner preimage retains exactly the same moved space. -/
theorem inner_preimage_moved (hF : Nat.card F = 4)
    (B : Subgroup (linearNormalizer (Natural.Normalizer.binary F)))
    [IsElementaryAbelian 2 B]
    (hm : Module.finrank (ZMod 2)
      (subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B) ≤ 4) :
    subspaceCommutator (Natural.Normalizer.binary F) ⊤
      (B.comap (normalizerEmbedding (Natural.Normalizer.binary F))) =
        subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B := by
  have hmap : (B.comap (normalizerEmbedding (Natural.Normalizer.binary F))).map
      (normalizerEmbedding (Natural.Normalizer.binary F)) = B :=
    Subgroup.map_comap_eq_self (small_moved_le_inner hF B hm)
  calc
    _ = subspaceCommutator
        ((normalizerRepresentation (Natural.Normalizer.binary F)).comp
          (normalizerEmbedding (Natural.Normalizer.binary F))) ⊤
        (B.comap (normalizerEmbedding (Natural.Normalizer.binary F))) := rfl
    _ = _ := by rw [subspaceCommutator_comp_map, hmap]

omit [Finite F] in
/-- Pullback along the faithful inner embedding preserves elementary actors. -/
theorem inner_preimage_elementary
    (B : Subgroup (linearNormalizer (Natural.Normalizer.binary F)))
    [IsElementaryAbelian 2 B] :
    IsElementaryAbelian 2 (B.comap (normalizerEmbedding (Natural.Normalizer.binary F))) :=
  IsElementaryAbelian.comap_of_injective _
    (normalizerEmbedding_injective _ (Natural.Normalizer.binary_faithful F)) B

/-- No centralizer or scalar kernel is lost when taking this inner preimage. -/
theorem inner_preimage_rank (hF : Nat.card F = 4)
    (B : Subgroup (linearNormalizer (Natural.Normalizer.binary F)))
    [IsElementaryAbelian 2 B]
    (hm : Module.finrank (ZMod 2)
      (subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B) ≤ 4) :
    rank (B.comap (normalizerEmbedding (Natural.Normalizer.binary F))) = rank B := by
  have hmap : (B.comap (normalizerEmbedding (Natural.Normalizer.binary F))).map
      (normalizerEmbedding (Natural.Normalizer.binary F)) = B :=
    Subgroup.map_comap_eq_self (small_moved_le_inner hF B hm)
  calc
    _ = rank ((B.comap (normalizerEmbedding (Natural.Normalizer.binary F))).map
        (normalizerEmbedding (Natural.Normalizer.binary F))) := by
      rw [rank, rank, Subgroup.card_map_of_injective
        (normalizerEmbedding_injective _ (Natural.Normalizer.binary_faithful F))]
    _ = _ := congrArg rank hmap

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
