module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OrientedAffineModelSource
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerLinearMarking
public import Theory.SpecificGroups.Alternating.CubicFiveThirty
public import Theory.SpecificGroups.GL2.FourCentralProduct

/-!
# Pointwise compatibility on all three original local intersections

The two markings of the original order-180 intersection agree on its
actual order-thirty subgroup by the point and full-pair equations. The
proved rigidity of C₃ × A₅ then forces agreement on the entire intersection.
This retains the original subgroup carriers and the full cubic factor.
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
theorem literal_canonical_three_pair_models
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
      (∀ x : (normalizer (A : Set G) ⊓ N : Subgroup G), ∃ z : LinearGroup,
        e₂ ⟨x,x.property.1⟩ = SemidirectProduct.inr z ∧
        e₃ ⟨x,x.property.2⟩ =
          (CubicNormalizerModel.linearThirdEquiv z : CubicNormalizerModel.Model)) ∧
      ∀ x : (L ⊓ N : Subgroup G),
        ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
          e₃ ⟨x,x.property.2⟩ =
            (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  let L := completion j.range (overlap j)
  let N := normalizer (zpowers (j cubic) : Set G)
  let M := normalizer (A : Set G)
  let E := M ⊓ N
  obtain ⟨K,e₁,e₃,e₂,hK,h₁,h₃,hV,hKm,hthird,hpoint,hC₂,hpointcompat,hpaircompat⟩ :=
    literal_canonical_affine_pair_models P hc A C l a hC ha j hj
  have hE : E = C.map M.subtype :=
    PlaneTransport.field_cubic_normalizer_intersection A C l a hC ha j hj
  have hEM : E.subgroupOf M = C := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show E ≤ M from inf_le_left),hE]
  have h₂ : (E.subgroupOf M).map e₂.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range := by
    rw [hEM,hC₂]
  have h₃E : (E.subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.thirdOverlap := by
    rw [show E.subgroupOf N = M.subgroupOf N from inf_subgroupOf_right M N]
    exact hthird
  let e₂E : E ≃* LinearGroup :=
    (subgroupOfEquivOfLe (show E ≤ M from inf_le_left)).symm.trans
      (((e₂.subgroupMap (E.subgroupOf M)).trans (MulEquiv.subgroupCongr h₂)).trans
        (MonoidHom.ofInjective (SemidirectProduct.inr_injective (φ := naturalAction))).symm)
  let e₃E : E ≃* CubicNormalizerModel.thirdOverlap :=
    (subgroupOfEquivOfLe (show E ≤ N from inf_le_right)).symm.trans
      ((e₃.subgroupMap (E.subgroupOf N)).trans (MulEquiv.subgroupCongr h₃E))
  have he₂E (x : E) : e₂ ⟨x,x.property.1⟩ = SemidirectProduct.inr (e₂E x) := by
    exact (congrArg Subtype.val
      ((MonoidHom.ofInjective (SemidirectProduct.inr_injective (φ := naturalAction))).apply_symm_apply
        ⟨e₂ ⟨x,x.property.1⟩,h₂ ▸ mem_map_of_mem e₂.toMonoidHom x.property⟩)).symm
  have he₃E (x : E) : (e₃E x : CubicNormalizerModel.Model) = e₃ ⟨x,x.property.2⟩ := rfl
  have hoE : overlap j ≤ E := by
    apply le_inf
    · exact (overlap_le j).trans hj.2.1
    · exact (overlap j).le_normalizer.trans (overlap_normalizer_le_cubic j hj.1)
  let U := (overlap j).subgroupOf E
  have hU : Nat.card U = 30 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hoE).toEquiv,
      Nat.card_congr (overlapEquiv j hj.1).toEquiv]
    simp [Seventeen.Complement,Nat.card_eq_fintype_card,Fintype.card_multiplicative,DihedralGroup.card]
  have hmaps : e₂E.trans CubicNormalizerModel.linearThirdEquiv = e₃E := by
    apply alternatingGroup.FiveLocalGeometry.CubicThirty.marked_equiv_ext
      (e₂E.trans Representation.SL2FourNatural.SemilinearNormalizer.cubicFiveEquiv) U hU
    intro x
    let xp : j.range := ⟨x,overlap_le j x.property⟩
    obtain ⟨z,hz₁,hz₂⟩ := hpointcompat xp
    have hxH : (x : G) ∈ L ⊓ N :=
      ⟨(show j.range ≤ L from le_sup_left) xp.property,x.val.property.2⟩
    obtain ⟨w,hw₁,hw₃⟩ := hpaircompat ⟨x,hxH⟩
    have hzw : (z : Theory.PSL2.BinaryFourFieldExtension.Model) = w := hz₁.symm.trans hw₁
    have hzC : z ∈ Seventeen.ModelAmalgam.C := by
      refine ⟨z.property,?_⟩
      change (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∈ Seventeen.ModelAmalgam.pair
      rw [hzw]
      exact w.property
    have hzmap : z ∈ BaumeisterParabolics.pointComplement.map
        Seventeen.ModelAmalgam.SingerPoint.pointEquiv.toMonoidHom :=
      Seventeen.ModelAmalgam.SingerPoint.pointEquiv_complement.symm ▸ hzC
    obtain ⟨q,hq,hqz⟩ := hzmap
    obtain ⟨n,rfl⟩ := hq
    have he₂n : e₂E x.val = SingerField.matrixEquiv n.val := by
      apply SemidirectProduct.inr_injective (φ := naturalAction)
      rw [←he₂E]
      change e₂ ⟨xp,hj.2.1 xp.property⟩ = _
      rw [hz₂,←hqz]
      change SingerField.affineEmbedding
        (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm
          (Seventeen.ModelAmalgam.SingerPoint.pointEquiv (SemidirectProduct.inr n))) = _
      rw [Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm_apply_apply]
      exact SemidirectProduct.map_inr _ _ _ n
    apply Subtype.ext
    change (CubicNormalizerModel.linearThirdEquiv (e₂E x.val) : CubicNormalizerModel.Model) = _
    rw [he₂n,CubicNormalizerModel.linearThirdEquiv_apply,he₃E,hw₃]
    apply congrArg (fun t : Seventeen.ModelAmalgam.pair =>
      (CubicNormalizerModel.modelPairEquiv t : CubicNormalizerModel.Model))
    apply Subtype.ext
    rw [CubicNormalizerModel.singerPair_coe]
    exact (congrArg Subtype.val hqz).trans hzw
  refine ⟨K,e₁,e₃,e₂,hK,h₁,h₃,hV,hKm,hthird,hpoint,hC₂,hpointcompat,?_,hpaircompat⟩
  intro x
  refine ⟨e₂E x,he₂E x,?_⟩
  have hh := congrArg (fun e : E ≃* CubicNormalizerModel.thirdOverlap =>
    (e x : CubicNormalizerModel.Model)) hmaps
  exact hh.symm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
