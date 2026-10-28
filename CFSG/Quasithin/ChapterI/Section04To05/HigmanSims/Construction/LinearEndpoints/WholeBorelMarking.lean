module
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.OppositeRadicalMarking
public import Theory.SpecificGroups.PSL3.SmallCompletion.AffineRadicalCoordinates
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-! Exact whole-Borel coordinates for the original natural endpoint and its
original order-192 common subgroup. Both radical images are retained. -/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
open Matrix.PSL3Even.UnipotentGeometry
variable {G : Type*} [Group G]

private theorem borel_card : Nat.card (borel F)=192 := by
  have hF : Nat.card F=4 := by rw [Nat.card_eq_fintype_card,card_field]
  have ht := BorelQuotient.card_torus_mul_scalar F
  rw [hF] at ht
  norm_num at ht
  have hc := (BorelQuotient.borel_complement F (n:=2) (by simpa using hF)).card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv,card_unipotent,hF] at hc
  omega

/-- Both original radicals and the entire original overlap are identified
inside the native line endpoint, retaining the actual quotient map. -/
theorem NaturalEndpointData.exists_whole_borel_marking {A : Subgroup G}
    [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (B : Subgroup G) [IsElementaryAbelian 2 B] (hB16 : Nat.card B=16)
    (hBP : B≤d.carrier) (hBA : B≤normalizer (A : Set G))
    (hR : U0.map d.embedding = ((d.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range)
    (J : Subgroup G) (hJP : J≤d.carrier) (hJN : J≤normalizer (B : Set G))
    (hJ192 : Nat.card J=192) :
    ∃ (f : d.carrier ≃* lineLocal F) (j : J ≃* borel F),
      (∀ g,(lineLocalEquivAffine F (f g)).right=d.quotient g) ∧
      (∀ a : A,lineLocalEquivAffine F (f (inclusion d.kernel_le a))=
        SemidirectProduct.inl (d.coordinates a)) ∧
      (A.subgroupOf d.carrier).map ((lineLocal F).subtype.comp f.toMonoidHom)=projectivePlane₂ F ∧
      (B.subgroupOf d.carrier).map ((lineLocal F).subtype.comp f.toMonoidHom)=projectivePlane₁ F ∧
      (∀ x : J,f (inclusion hJP x)=lineBorelInclusion (j x)) := by
  obtain ⟨a,haq,hak,haA,haB,_⟩ := d.exists_opposite_radical_marking B hB16 hBP hBA hR
  let f := a.trans (lineLocalEquivAffine F).symm
  let g := (lineLocal F).subtype.comp f.toMonoidHom
  have hg : Function.Injective g := Subtype.val_injective.comp f.injective
  have hA : (A.subgroupOf d.carrier).map g=projectivePlane₂ F := by
    change (A.subgroupOf d.carrier).map (affineLineEmbedding.comp a.toMonoidHom)=_
    rw [←Subgroup.map_map,haA,affineLineEmbedding_translations]
  have hB : (B.subgroupOf d.carrier).map g=projectivePlane₁ F := by
    change (B.subgroupOf d.carrier).map (affineLineEmbedding.comp a.toMonoidHom)=_
    rw [←Subgroup.map_map,haB,affineLineEmbedding_opposite]
  have hJ : (J.subgroupOf d.carrier).map g=borel F := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      apply line_normalizer_opposite_le_borel
      refine ⟨(f x).property,?_⟩
      rw [←hB]
      apply (B.subgroupOf d.carrier).le_normalizer_map g
      apply mem_map_of_mem
      rw [←subgroupOf_normalizer_eq hBP]
      exact hJN hx
    · rw [card_map_of_injective hg,
        Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv,hJ192,borel_card]
  let j : J ≃* borel F := (subgroupOfEquivOfLe hJP).symm.trans
    (((J.subgroupOf d.carrier).equivMapOfInjective g hg).trans (MulEquiv.subgroupCongr hJ))
  refine ⟨f,j,?_,?_,hA,hB,fun _ => Subtype.ext rfl⟩
  · intro x
    change ((lineLocalEquivAffine F) ((lineLocalEquivAffine F).symm (a x))).right=_
    rw [MulEquiv.apply_symm_apply,haq]
  · intro x
    change (lineLocalEquivAffine F) ((lineLocalEquivAffine F).symm (a (inclusion d.kernel_le x)))=_
    rw [MulEquiv.apply_symm_apply,hak]

end CFSG.Quasithin.HigmanSims
