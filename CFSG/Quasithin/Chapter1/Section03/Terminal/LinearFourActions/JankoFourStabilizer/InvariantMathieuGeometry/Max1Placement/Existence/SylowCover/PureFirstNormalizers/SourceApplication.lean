module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.Max4Endpoint
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Applications
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Ordinary

/-!
# Pure-first endpoint refinement of the actual nonsingular source reduction

The source row reduction supplies a pure witness with exactly the original
whole normalizer. If this witness is a conjugate of the certified max4 eight,
the existing full normalizer theorem gives the literal max4 endpoint. It cannot
be a conjugate of the distinguished plane, since that plane's normalizer is
strictly contained in the max4 two-local.

The remaining order-256 normalizer is consumed only through the fixed native
normalizer-to-F placement. This is the same independent premise used in KW
Section 2.1; no invariant-isotropic-subgroup shortcut is used. The residual
pure witness is retained with both literal small-model exclusions. Its complete
line/extraspecial/sextet classification remains the pure-geometry producer's
obligation. No claim of a complete four-local cover is made here.

Source: Kleidman--Wilson (1988), Sections 2.1 and 2.3, pp.488--493.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers
open SymmetricLinear ElementaryNormalizerCover
open Cardinality.QuotientCount.Image
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

/-- Refine the actual source maximal-normalizer alternative at the proved
max4 endpoint. The fixed native order-256 placement stays explicit; all
remaining pure witnesses avoid the certified max4 plane and eight. -/
theorem source_maximal_reduction_at_max4
    (h8 : PureTwoA.EightNormalizerPlacement)
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
        pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ NonsingularImages.boxImage) ∨
    (∃ g : Model,
      normalizer (X : Set Model) = LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max4Subgroup.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      (∀ z ∈ Z, z ≠ 1 → IsConj a z) ∧
      (¬ ∃ g : Model, Z = max4Plane.map (MulAut.conj g).toMonoidHom) ∧
      (¬ ∃ g : Model, Z = max4Eight.map (MulAut.conj g).toMonoidHom)) := by
  rcases NonsingularImages.source_maximal_reduction X hs hp hM with
    hbox | ⟨g, hF | hE⟩ | ⟨Z, hZ, hZe, hNZ, hpure⟩ | ⟨g, hg⟩
  · exact Or.inl hbox
  · exact Or.inr (Or.inl ⟨g, Or.inl hF⟩)
  · exact Or.inr (Or.inl ⟨g, Or.inr (Or.inl hE)⟩)
  · by_cases he : ∃ g : Model, Z = max4Eight.map (MulAut.conj g).toMonoidHom
    · obtain ⟨g, hg⟩ := he
      exact Or.inr (Or.inl ⟨g, Or.inr (Or.inr
        (max4_endpoint_of_eight_witness X Z g hNZ hg))⟩)
    · exact Or.inr (Or.inr ⟨Z, hZ, hZe, hNZ, hpure,
        source_witness_not_plane X Z hM hNZ, he⟩)
  · obtain ⟨k, hk⟩ := h8
    have hn : normalizer (X : Set Model) ≤
        LinearFive.fullNormalizer.map (MulAut.conj (g*k)).toMonoidHom := by
      rw [hg]
      have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hk
      rw [map_map] at ht
      have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
          (MulAut.conj (g*k)).toMonoidHom := by
        ext x
        simp [mul_assoc]
      rwa [hc] at ht
    have hlocal : IsTwoLocal LinearFive.fullNormalizer := by
      rw [← LinearFive.M_F_eq_fullNormalizer]
      exact nativeF_generated_isTwoLocal
    have he := hM.eq_of_le (hlocal.map_equiv (MulAut.conj (g*k))) hn
    rw [← LinearFive.M_F_eq_fullNormalizer] at he
    exact Or.inr (Or.inl ⟨g*k, Or.inl he⟩)

end Janko4.LocalStructure.PureFirstNormalizers
