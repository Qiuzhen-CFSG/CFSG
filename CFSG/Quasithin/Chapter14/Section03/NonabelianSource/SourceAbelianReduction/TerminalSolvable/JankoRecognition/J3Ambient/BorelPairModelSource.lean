module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.ThirdOverlapModelSource
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.CompatiblePairMapsForm
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairBorelGeometry

/-!
# Retaining the two original Borel choices in the simultaneous marking

The original sixteen-field recognition marks the point subgroup exactly.
Retaining the inner and field form of its pair correction shows that the
resulting map sends that subgroup to one of the two canonical Borels.
The cubic map continues to retain the original complement and third overlap.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The original source supplies full pair agreement and the fixed third
overlap simultaneously, with its same chosen cubic complement and kernel.
No subgroup-alignment or third-overlap hypothesis is added. -/
theorem literal_canonical_third_pair_models_two_borels
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let L := completion j.range (overlap j)
    let N := normalizer (zpowers (j cubic) : Set G)
    ∃ (K : Subgroup N) (e₁ : L ≃* Theory.PSL2.BinaryFourFieldExtension.Model)
      (e₃ : N ≃* CubicNormalizerModel.Model),
      (cubicNormalizerKernel (j cubic)).IsComplement' K ∧
      ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
        Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair ∧
      ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair ∧
      (cubicNormalizerKernel (j cubic)).map e₃.toMonoidHom =
        CubicNormalizerModel.projection.ker ∧
      K.map e₃.toMonoidHom =
        (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range ∧
      ((normalizer (A : Set G)).subgroupOf N).map e₃.toMonoidHom =
        CubicNormalizerModel.thirdOverlap ∧
      (((j.range).subgroupOf L).map e₁.toMonoidHom =
        Seventeen.ModelAmalgam.point ∨
        ((j.range).subgroupOf L).map e₁.toMonoidHom =
          Seventeen.ModelAmalgam.oppositePoint) ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ =
            (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  obtain ⟨K,_,e₃,hK,_,h₃,hV,hKm,hthird,_⟩ :=
    literal_canonical_third_pair_models P hc A C l a hC ha j hj
  let mark := Janko23.J3Recognition.Ambient.BaumeisterParabolics.original_marking_of_pair_triangle
    j hj.1 (literal_overlap_pair_equiv P hc A C a j hj).some
    (literal_triangle_equiv P hc A C a j hj).some
  obtain ⟨e₀,hpoint,hpair,_,_⟩ := mark.recognition
  have hi : L ⊓ N = normalizer (overlap j : Set G) :=
    literal_completion_cubic_normalizer_intersection P hc A C a j hj
  have h₀ : ((L ⊓ N).subgroupOf L).map e₀.toMonoidHom =
      Seventeen.ModelAmalgam.pair := by
    rw [hi]
    exact hpair
  obtain ⟨e₁,c,δ,he₁,h₁,hcompat⟩ :=
    Seventeen.ModelAmalgam.compatible_pair_maps_inner_field L N
      CubicNormalizerModel.pair e₀ e₃ h₀ h₃ CubicNormalizerModel.modelPairEquiv
  refine ⟨K,e₁,e₃,hK,h₁,h₃,hV,hKm,hthird,?_,hcompat⟩
  have hF : ((j.range).subgroupOf L).map e₁.toMonoidHom =
      Seventeen.ModelAmalgam.point.map
        (MulAut.conj (c : Theory.PSL2.BinaryFourFieldExtension.Model)).toMonoidHom := by
    rw [he₁]
    change ((j.range).subgroupOf L).map
      (((MulAut.conj (c : Theory.PSL2.BinaryFourFieldExtension.Model) *
        (if δ then Seventeen.ModelAmalgam.squareModel else 1)).toMonoidHom).comp
        e₀.toMonoidHom) = _
    rw [←map_map,hpoint]
    cases δ
    · rfl
    · change Seventeen.ModelAmalgam.point.map
        ((MulAut.conj (c : Theory.PSL2.BinaryFourFieldExtension.Model)).toMonoidHom.comp
          Seventeen.ModelAmalgam.squareModel.toMonoidHom) = _
      rw [←map_map,Seventeen.ModelAmalgam.squareModel_point]
  rw [hF]
  exact Seventeen.ModelAmalgam.pair_conj_point_or_opposite c

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
