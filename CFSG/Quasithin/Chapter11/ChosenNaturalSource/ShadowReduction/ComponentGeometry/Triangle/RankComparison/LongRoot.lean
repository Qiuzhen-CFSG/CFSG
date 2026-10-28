module
public import Theory.Representation.G2NaturalSmallMovedRoot
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Inner

/-!
# The full-normalizer small-moved actor lies in a long-root group

The preceding field-part exclusion places the original normalizer subgroup
inside the faithful inner image. Pullback preserves its actual moved space
and rank. The natural-module fixed-space theorem then places that preimage
in a single conjugate highest-root group. Mapping back retains the original
normalizer action and gives its rank-two bound.

Source: Aschbacher–Smith 11.4.1(2), p.776.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
attribute [local instance] ZMod.algebra
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- A small-moved elementary subgroup of the full normalizer is contained
in the image of an actual conjugate highest-root group. -/
theorem small_moved_le_longRoot_image (hF : Nat.card F = 4)
    (B : Subgroup (linearNormalizer (Natural.Normalizer.binary F)))
    [IsElementaryAbelian 2 B]
    (hm : Module.finrank (ZMod 2)
      (subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B) ≤ 4) :
    ∃ g : Model F, B ≤
      (LieParabolicSetup.highestRoot.map (MulAut.conj g).toMonoidHom).map
        (normalizerEmbedding (Natural.Normalizer.binary F)) := by
  let C := B.comap (normalizerEmbedding (Natural.Normalizer.binary F))
  let : IsElementaryAbelian 2 C := inner_preimage_elementary B
  have hc : Module.finrank (ZMod 2)
      (subspaceCommutator (Natural.Normalizer.binary F) ⊤ C) ≤ 4 := by
    rw [inner_preimage_moved hF B hm]
    exact hm
  obtain ⟨g,hg⟩ := NaturalSmallMovedRoot.exists_le_highestRoot hF C hc
  refine ⟨g, ?_⟩
  have he : C.map (normalizerEmbedding (Natural.Normalizer.binary F)) = B :=
    Subgroup.map_comap_eq_self (small_moved_le_inner hF B hm)
  rw [← he]
  exact Subgroup.map_mono hg

/-- The faithful inner pullback loses neither movement nor binary rank. -/
theorem small_moved_rank_le_two (hF : Nat.card F = 4)
    (B : Subgroup (linearNormalizer (Natural.Normalizer.binary F)))
    [IsElementaryAbelian 2 B]
    (hm : Module.finrank (ZMod 2)
      (subspaceCommutator (normalizerRepresentation (Natural.Normalizer.binary F)) ⊤ B) ≤ 4) :
    rank B ≤ 2 := by
  let C := B.comap (normalizerEmbedding (Natural.Normalizer.binary F))
  let : IsElementaryAbelian 2 C := inner_preimage_elementary B
  have hc : Module.finrank (ZMod 2)
      (subspaceCommutator (Natural.Normalizer.binary F) ⊤ C) ≤ 4 := by
    rw [inner_preimage_moved hF B hm]
    exact hm
  rw [← inner_preimage_rank hF B hm]
  exact NaturalSmallMovedRoot.rank_le_two hF C hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
