module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.BorelPairModelSource
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.CubicPairBorelInversion

/-!
# The original Borel, full pair, and third overlap marked simultaneously

A pair involution exchanges the two canonical Borels. On the entire common
pair its conjugation agrees with cubic-kernel inversion on the other model.
Applying these two automorphisms together restores the original Borel and
retains pointwise full-pair agreement, the same cubic complement, its kernel,
and the complete third overlap. All markings are constructed from the
original geometry.
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
theorem literal_canonical_borel_third_pair_models
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
      ((j.range).subgroupOf L).map e₁.toMonoidHom =
        Seventeen.ModelAmalgam.point ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ =
            (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  obtain ⟨K,e₁,e₃,hK,h₁,h₃,hV,hKm,hthird,hpoint,hcompat⟩ :=
    literal_canonical_third_pair_models_two_borels P hc A C l a hC ha j hj
  rcases hpoint with hpoint | hopposite
  · exact ⟨K,e₁,e₃,hK,h₁,h₃,hV,hKm,hthird,hpoint,hcompat⟩
  obtain ⟨b,_hb,_hbpoint,hbopposite,hbcompat⟩ :=
    Seventeen.ModelAmalgam.exists_pair_borel_inversion CubicNormalizerModel.modelPairEquiv
  let β := MulAut.conj (b : Theory.PSL2.BinaryFourFieldExtension.Model)
  let κ := CubicNormalizerModel.kernelInversion
  have hβ : Seventeen.ModelAmalgam.pair.map β.toMonoidHom =
      Seventeen.ModelAmalgam.pair :=
    mem_normalizer_iff_map_conj_eq.mp (Seventeen.ModelAmalgam.pair.le_normalizer b.property)
  have hκpair : CubicNormalizerModel.pair.map κ.toMonoidHom =
      CubicNormalizerModel.pair :=
    CubicNormalizerModel.kernelInversion_preimage CubicNormalizerModel.projectivePair
  have hκker : CubicNormalizerModel.projection.ker.map κ.toMonoidHom =
      CubicNormalizerModel.projection.ker := by
    exact CubicNormalizerModel.kernelInversion_preimage ⊥
  have hκcomp :
      (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range.map
        κ.toMonoidHom =
      (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range := by
    apply le_antisymm
    · rintro _ ⟨x,⟨p,rfl⟩,rfl⟩
      exact ⟨p,(CubicNormalizerModel.kernelInversion_inr p).symm⟩
    · rintro _ ⟨p,rfl⟩
      exact ⟨SemidirectProduct.inr p,⟨p,rfl⟩,CubicNormalizerModel.kernelInversion_inr p⟩
  have hκthird : CubicNormalizerModel.thirdOverlap.map κ.toMonoidHom =
      CubicNormalizerModel.thirdOverlap :=
    CubicNormalizerModel.kernelInversion_preimage CubicNormalizerModel.thirdFive
  refine ⟨K,e₁.trans β,e₃.trans κ,hK,?_,?_,?_,?_,?_,?_,?_⟩
  · change ((L ⊓ N).subgroupOf L).map (β.toMonoidHom.comp e₁.toMonoidHom) = _
    rw [←map_map,h₁,hβ]
  · change ((L ⊓ N).subgroupOf N).map (κ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,h₃,hκpair]
  · change (cubicNormalizerKernel (j cubic)).map (κ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,hV,hκker]
  · change K.map (κ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,hKm,hκcomp]
  · change ((normalizer (A : Set G)).subgroupOf N).map
      (κ.toMonoidHom.comp e₃.toMonoidHom) = _
    rw [←map_map,hthird,hκthird]
  · change ((j.range).subgroupOf L).map (β.toMonoidHom.comp e₁.toMonoidHom) = _
    rw [←map_map,hopposite]
    exact hbopposite
  · intro x
    obtain ⟨z,hz₁,hz₃⟩ := hcompat x
    refine ⟨MulAut.conj b z,?_,?_⟩
    · change β (e₁ ⟨x,x.property.1⟩) = _
      rw [hz₁]
      rfl
    · change κ (e₃ ⟨x,x.property.2⟩) = _
      rw [hz₃]
      exact hbcompat z

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
