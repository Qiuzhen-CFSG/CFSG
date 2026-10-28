module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicNormalizerModelSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CompletionCubicIntersection
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.CompatiblePairMaps

/-!
# Simultaneous local models on the original full pair

The original geometric source supplies both model maps and their full pair
images. Every automorphism of the sixteen-field pair extends to its local
group. Thus any fixed identification of the two model pairs can be realized
pointwise on the entire original intersection.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- Both local maps realize a prescribed model-pair identification on every
element of their actual original intersection. -/
theorem literal_compatible_pair_model_maps
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j)
    (ε : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair ≃*
      CubicNormalizerModel.pair) :
    let L := completion j.range (overlap j)
    let N := normalizer (zpowers (j cubic) : Set G)
    ∃ (e₁ : L ≃* Theory.PSL2.BinaryFourFieldExtension.Model)
      (e₃ : N ≃* CubicNormalizerModel.Model),
      ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
        Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair ∧
      ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair ∧
      (cubicNormalizerKernel (j cubic)).map e₃.toMonoidHom =
        CubicNormalizerModel.projection.ker ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ = (ε z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  let mark := Janko23.J3Recognition.Ambient.BaumeisterParabolics.original_marking_of_pair_triangle
    j hj.1 (literal_overlap_pair_equiv P hc A C a j hj).some
    (literal_triangle_equiv P hc A C a j hj).some
  obtain ⟨e₁,_,hpair,_,_⟩ := mark.recognition
  obtain ⟨e₃,hpair₃,hkernel⟩ := literal_cubic_normalizer_model_pair P hc A C l a ha j hj
  have hi : L ⊓ N = normalizer (overlap j : Set G) :=
    literal_completion_cubic_normalizer_intersection P hc A C a j hj
  have h₁ : ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
      Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair := by
    rw [hi]
    exact hpair
  have h₃ : ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair := by
    rw [hi]
    exact hpair₃
  obtain ⟨f,hf,hcompat⟩ := Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.compatible_pair_maps
    L N CubicNormalizerModel.pair e₁ e₃ h₁ h₃ ε
  exact ⟨f,e₃,hf,h₃,hkernel,hcompat⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
