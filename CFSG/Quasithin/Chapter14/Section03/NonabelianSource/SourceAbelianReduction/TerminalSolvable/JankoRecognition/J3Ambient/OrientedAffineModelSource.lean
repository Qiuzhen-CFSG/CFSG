module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OrientedBorelPairModelSource
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.SingerPointEquiv
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerFieldAffineExtension.Source

/-!
# Extend the original oriented Borel marking to its affine normalizer

The same original sixteen-field marking restricts to the point subgroup.
Its literal order-thirty overlap is carried to the canonical point-pair
intersection. The genuine Singer point coordinates and affine extension
therefore construct an affine marking agreeing on every point-subgroup
element. The original full linear complement is retained. Full agreement
of the two maps on the order-180 third overlap is a subsequent obligation.
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
theorem literal_canonical_affine_pair_models
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
      (e₃ : N ≃* CubicNormalizerModel.Model)
      (e₂ : normalizer (A : Set G) ≃* Plane ⋊[naturalAction] LinearGroup),
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
      C.map e₂.toMonoidHom =
        (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range ∧
      (∀ x : j.range, ∃ z : Seventeen.ModelAmalgam.point,
        e₁ ⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
        e₂ ⟨x,hj.2.1 x.property⟩ =
          SingerField.affineEmbedding (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm z)) ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ =
            (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  obtain ⟨K,e₁,e₃,hK,h₁,h₃,hV,hKm,hthird,hpoint,hcompat⟩ :=
    literal_canonical_borel_third_pair_models P hc A C l a hC ha j hj
  let ep : j.range ≃* Seventeen.ModelAmalgam.point :=
    (subgroupOfEquivOfLe (show j.range ≤ L from le_sup_left)).symm.trans
      ((e₁.subgroupMap ((j.range).subgroupOf L)).trans (MulEquiv.subgroupCongr hpoint))
  have hep (x : j.range) : (ep x : Theory.PSL2.BinaryFourFieldExtension.Model) =
      e₁ ⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ := rfl
  have hi : L ⊓ N = normalizer (overlap j : Set G) :=
    literal_completion_cubic_normalizer_intersection P hc A C a j hj
  have ho : j.range ⊓ (L ⊓ N) = overlap j := by
    rw [hi,point_intersection_normalizer j hj.1]
  have hepc : ((overlap j).subgroupOf j.range).map ep.toMonoidHom =
      Seventeen.ModelAmalgam.C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change (ep x : Theory.PSL2.BinaryFourFieldExtension.Model) ∈
        Seventeen.ModelAmalgam.point ⊓ Seventeen.ModelAmalgam.pair
      refine ⟨(ep x).property,?_⟩
      rw [hep]
      apply h₁ ▸ mem_map_of_mem e₁.toMonoidHom
        (show (⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ : L) ∈ (L ⊓ N).subgroupOf L from ?_)
      exact ((show (x : G) ∈ j.range ⊓ (L ⊓ N) from ho.symm ▸ hx)).2
    · intro z hz
      obtain ⟨x,rfl⟩ := ep.surjective z
      have hzpair : e₁ ⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ ∈ Seventeen.ModelAmalgam.pair := by
        rw [←hep]
        exact hz.2
      rw [←h₁] at hzpair
      obtain ⟨u,hu,he⟩ := hzpair
      have heu : u = ⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ := e₁.injective he
      have hxH : (x : G) ∈ L ⊓ N := by
        change (⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ : L) ∈
          (L ⊓ N).subgroupOf L
        rw [←heu]
        exact hu
      exact ⟨x,ho ▸ ⟨x.property,hxH⟩,rfl⟩
  let e : j.range ≃* SingerField.Model :=
    ep.trans Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm
  have he : ((overlap j).subgroupOf j.range).map e.toMonoidHom =
      BaumeisterParabolics.pointComplement := by
    change ((overlap j).subgroupOf j.range).map
      (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm.toMonoidHom.comp ep.toMonoidHom) = _
    rw [←map_map,hepc,←Seventeen.ModelAmalgam.SingerPoint.pointEquiv_complement,map_map]
    have hcomp : Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm.toMonoidHom.comp
        Seventeen.ModelAmalgam.SingerPoint.pointEquiv.toMonoidHom =
        MonoidHom.id SingerField.Model := by
      apply MonoidHom.ext
      intro x
      exact Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm_apply_apply x
    rw [hcomp,map_id]
  obtain ⟨e₂,hC₂,he₂⟩ := PlaneTransport.affine_equiv_extending_original_point_marking
    A C l a hC ha j hj e he
  refine ⟨K,e₁,e₃,e₂,hK,h₁,h₃,hV,hKm,hthird,hpoint,hC₂,?_,hcompat⟩
  intro x
  exact ⟨ep x,(hep x).symm,he₂ x⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
