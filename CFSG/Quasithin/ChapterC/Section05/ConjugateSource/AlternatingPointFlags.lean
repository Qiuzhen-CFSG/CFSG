module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.BorelGeometry
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelMarked
public import Theory.Representation.BinaryAlternatingFiveExtension.PointCoreGeometry.Transport

/-!
# The intrinsic point-core flags in the original block coordinates

The natural A₅ extension splits with its original kernel marking. Its
standard point Borel therefore has a semidirect-product equivalence that
preserves every vector under the given block coordinates. Transporting the
residual two-core and its center identifies the literal source intersection
Uᵢ ∩ Rᵢ with the marked three-space and Z(Rᵢ) with the marked fixed line.

These equalities retain the original block action. They supply the intrinsic
flags used to exchange the two source factors in the 14.6.9(k) argument.

Source: Aschbacher--Smith, C.5.6 and 14.6.9(i,k), printed pp.1025--1027
(refs/quasithin.pdf).
-/

public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The literal point-centralizer Borel preserves the original module coordinates
pointwise on its vector subgroup. -/
theorem AlternatingPairSetup.central_point_borel_marked
    (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (z : G) (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (hout : ¬ K ≤ centralizer ({z} : Set G)) :
    ∃ eb : (K ⊓ centralizer ({z} : Set G) : Subgroup G) ≃*
      AlternatingFiveExtension.BorelModel, ∀ v : AlternatingFiveExtension.V,
      (eb.symm (SemidirectProduct.inl v) : G) = h.borelMap v := by
  let q : K →* alternatingGroup (Fin 5) :=
    { toFun := fun k => ⟨h.action (inclusion le_sup_left k),by
        rw [←h.block_image]
        exact mem_map_of_mem h.action k.property⟩
      map_one' := Subtype.ext (h.action.map_one)
      map_mul' := fun k l => Subtype.ext (by
        exact h.action.map_mul (inclusion le_sup_left k) (inclusion le_sup_left l)) }
  have hq : Function.Surjective q := by
    intro a
    have ha : a.val ∈ (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action :=
      h.block_image.symm ▸ a.property
    obtain ⟨k,hk,he⟩ := ha
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hcore := h.block_core_eq_module x hx hnc
  have hker : q.ker = blockU K := by
    ext k
    rw [←hcore,←h.block.2.1.centralizer_blockU]
    constructor
    · intro hk u hu
      have hk' : inclusion le_sup_left k ∈ h.action.ker :=
        congrArg Subtype.val hk
      rw [h.action_kernel] at hk'
      exact Subtype.ext (hk' u (mem_map_of_mem K.subtype hu))
    · intro hk
      apply Subtype.ext
      change inclusion le_sup_left k ∈ h.action.ker
      rw [h.action_kernel]
      rintro u ⟨v,hv,rfl⟩
      exact congrArg Subtype.val (hk v hv)
  let eu : q.ker ≃* sourceModule K := (MulEquiv.subgroupCongr hker).trans
    ((blockU K).equivMapOfInjective K.subtype K.subtype_injective)
  let e := eu.trans h.coordinates
  have he (k : K) (v : q.ker) : e (MulAut.conjNormal k v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q k).val (e v).toAdd) := by
    apply h.coordinates.symm.injective
    change h.coordinates.symm (h.coordinates (eu (MulAut.conjNormal k v))) =
      h.coordinates.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (h.action (inclusion le_sup_left k)) (h.coordinates (eu v)).toAdd))
    rw [h.coordinates.symm_apply_apply]
    apply Subtype.ext
    exact (h.equivariant (inclusion le_sup_left k) (eu v)).symm
  obtain ⟨_,_,_,hmark⟩ := h.central_point_marking z hzS hzR hout
  let B := (MulAction.stabilizer (alternatingGroup (Fin 5)) (4 : Fin 5)).comap q
  have hB : B = (centralizer ({z} : Set G)).subgroupOf K := by
    ext k
    exact (hmark k).symm
  obtain ⟨eb, heb⟩ := AlternatingFiveExtension.standard_borel_equiv_marked q hq e he
  let ef : (centralizer ({z} : Set G)).subgroupOf K ≃*
      (K ⊓ centralizer ({z} : Set G) : Subgroup G) :=
    { toFun := fun k => ⟨k,⟨k.val.property,k.property⟩⟩
      invFun := fun k => ⟨⟨k,k.property.1⟩,k.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨ef.symm.trans ((MulEquiv.subgroupCongr hB.symm).trans eb), ?_⟩
  intro v
  have heu (u : q.ker) : ((u : K) : G) = (eu u : G) := rfl
  refine (congrArg Subtype.val (heb v)).trans ((heu _).trans ?_)
  apply congrArg Subtype.val
  apply h.coordinates.injective
  exact (e.apply_symm_apply v).trans (h.coordinates.apply_symm_apply v).symm

/-- The source three-space and central line use the original block coordinates. -/
theorem AlternatingPairSetup.central_point_flags
    (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (z : G) (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (hout : ¬ K ≤ centralizer ({z} : Set G)) :
    let H := K ⊓ centralizer ({z} : Set G)
    let X := (pResidual 2 H).map H.subtype
    let N := X.pCoreIn 2
    sourceModule K ⊓ N = AlternatingFiveFlag.three.map h.borelMap ∧
      (center N).map N.subtype = AlternatingFiveFlag.line.map h.borelMap := by
  let H := K ⊓ centralizer ({z} : Set G)
  obtain ⟨e,he⟩ := h.central_point_borel_marked x hx hnc z hzS hzR hout
  let : Finite AlternatingFiveExtension.BorelModel := Finite.of_equiv H e.toEquiv
  let f : AlternatingFiveExtension.BorelModel →* G := H.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp e.symm.injective
  have hfi : f.comp SemidirectProduct.inl = h.borelMap := MonoidHom.ext he
  have hA : AlternatingFiveExtension.PointCoreGeometry.vectors.map f = sourceModule K := by
    rw [AlternatingFiveExtension.PointCoreGeometry.vectors,
      ←SemidirectProduct.range_inl_eq_ker_rightHom,MonoidHom.map_range,hfi]
    change ((sourceModule K).subtype.comp h.coordinates.symm.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective _ h.coordinates.symm.surjective,
      ←MonoidHom.range_eq_map]
    exact (sourceModule K).range_subtype
  have hX : (pResidual 2 AlternatingFiveExtension.BorelModel).map f =
      (pResidual 2 H).map H.subtype := by
    change (pResidual 2 AlternatingFiveExtension.BorelModel).map
      (H.subtype.comp e.symm.toMonoidHom) = _
    rw [←map_map,map_pResidual_of_surjective 2 e.symm.toMonoidHom e.symm.surjective]
  have hN : AlternatingFiveExtension.coreModel.map f = ((pResidual 2 H).map H.subtype).pCoreIn 2 := by
    rw [←AlternatingFiveExtension.PointCoreGeometry.residual_pCoreIn_eq_coreModel,
      map_pCoreIn_of_injective 2 _ f hf,hX]
  have hthree : AlternatingFiveExtension.PointCoreGeometry.vectors ⊓
      AlternatingFiveExtension.coreModel = AlternatingFiveExtension.PointCoreGeometry.threeSpace := by
    apply le_antisymm
    · intro a ha
      exact ⟨ha.1,ha.2.1⟩
    · intro a ha
      exact ⟨ha.1,ha.2,AlternatingFiveExtension.PointCoreGeometry.vectors_le_outerCore ha.1⟩
  constructor
  · change sourceModule K ⊓ ((pResidual 2 H).map H.subtype).pCoreIn 2 = _
    rw [←hA,←hN,←map_inf _ _ _ hf,hthree,
      AlternatingFiveExtension.PointCoreGeometry.threeSpace_eq_map,map_map,hfi]
  · obtain ⟨_,_,_,_,hz⟩ := AlternatingFiveExtension.PointCoreGeometry.mapped_geometry f hf
    rw [hN] at hz
    rw [hz,AlternatingFiveExtension.PointCoreGeometry.fixedLine,map_map,hfi]
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
