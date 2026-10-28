module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedCoreImage
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.LiteralMovedCover
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The original module inside the literal classified moved space

For a normal A₅ seed in the selected constrained component, the original
module embeds in the actual component-moved star space. Under any group
marking of that space's actor, it is fully moved by the literal seed image
and fixed by its complete two-core. Original component-centralizing points
remain globally fixed, with their original group elements unchanged.

This is the common module transport for the symplectic and G₂ natural-cover
exclusions in Aschbacher--Smith C.4.8 and 12.7.5, printed pp.154 and 840.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource

private theorem literal_star_section {G : Type*} [Group G] [Finite G] (K R : Subgroup G) :
    ∃ d : BinaryConjugationSection (K ⊔ R)
      ((starV K R).map (K ⊔ R).subtype) ⊥
      ((starRepresentation K R).comp (QuotientGroup.mk' (starKernel K R))),
      ∀ v, ((((d.coordinates v).toAdd.toMul : starV K R) : (K ⊔ R : Subgroup G)) : G) = v := by
  let S := K ⊔ R
  let U := starV K R
  let Ug := U.map S.subtype
  let e := U.equivMapOfInjective S.subtype S.subtype_injective
  have he (v : Ug) : (((e.symm v : U) : S) : G) = v :=
    congrArg Subtype.val (e.apply_symm_apply v)
  let c : Ug →* Multiplicative (Additive U) := {
    toFun v := Multiplicative.ofAdd (Additive.ofMul (e.symm v))
    map_one' := by rw [map_one]; rfl
    map_mul' _ _ := by rw [map_mul]; rfl }
  have hn : S ≤ normalizer (Ug : Set G) := by
    have hh := U.le_normalizer_map S.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨{
    section_le := map_subtype_le U
    kernel_le := bot_le
    normalized := hn
    coordinates := c
    onto := fun (w : Multiplicative (Additive U)) => ⟨e w.toAdd.toMul,congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x))
      (e.symm_apply_apply _)⟩
    kernel_eq := ?_
    equivariant := ?_ },he⟩
  · ext v
    change e.symm v = 1 ↔ (v : G) = 1
    rw [e.symm.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  · intro x v
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    simp only [MonoidHom.comp_apply]
    rw [starRepresentation_apply]
    change (((e.symm _) : S) : G) = (x : G) * (((e.symm v) : S) : G) * (x : G)⁻¹
    rw [he,he]

private theorem original_subgroup_star_map
    {G : Type*} [Group G] {K R A : Subgroup G} (hAK : A ≤ K) :
    (A.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' (starKernel K R)) =
      (A.subgroupOf K).map ((starImage K R K).subtype.comp (toStarImage K R)) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,hAK ha⟩,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,mem_sup_left a.property⟩,ha,rfl⟩

set_option maxHeartbeats 800000 in
/-- The unchanged original module is core-fixed and fully moved inside the
literal moved carrier, compatibly with any marking of its actual actor. -/
theorem constrained_normal_seed_moved_module
    {G D : Type*} [Group G] [Finite G] [Group D]
    {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (eA5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (s : MovedSection ((starRepresentation (J.map H.subtype) R).comp
      (offenderSubgroup (starRepresentation (J.map H.subtype) R)).subtype)
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))))
    (e : ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))) ≃* D) :
    let K := J.map H.subtype
    let ρ := starRepresentation K R
    let O := offenderSubgroup ρ
    let C := starImage K R K
    let hCO := (C27Source.star_moved_section_from_source
      (h.constrained_source_input J hJ hq hout hf)).1
    let q := (e.toMonoidHom.comp (subgroupOfEquivOfLe hCO).symm.toMonoidHom).comp
      (toStarImage K R)
    let B := (L.subgroupOf K).map q
    let σ := s.space.toRepresentation.comp ((C.subgroupOf O).subtype.comp e.symm.toMonoidHom)
    ∃ A : Submodule (ZMod 2) s.space.toSubmodule,
      A ≤ fixedSpace σ (B.pCoreIn 2) ∧ subspaceCommutator σ A B = A ∧
      ∀ v : V, ∃ w : s.space.toSubmodule, w ∈ A ∧
        (((w.val.toMul : starV K R) : (K ⊔ R : Subgroup G)) : G) = v ∧
        ((v : G) ∈ centralizer (K : Set G) → w ∈ Representation.OneCohomology.fixed σ) := by
  let K := J.map H.subtype
  let S := K ⊔ R
  let ρ := starRepresentation K R
  let O := offenderSubgroup ρ
  let C := starImage K R K
  let π := QuotientGroup.mk' (starKernel K R)
  have hi := h.constrained_source_input J hJ hq hout hf
  have hCO : C ≤ O := (C27Source.star_moved_section_from_source hi).1
  let eC := subgroupOfEquivOfLe hCO
  let E := eC.symm.trans e
  let q : K →* D := E.toMonoidHom.comp (toStarImage K R)
  let B := (L.subgroupOf K).map q
  let σ : Representation (ZMod 2) D s.space.toSubmodule :=
    s.space.toRepresentation.comp ((C.subgroupOf O).subtype.comp e.symm.toMonoidHom)
  have hLK : L ≤ K := by
    intro l hl
    exact ⟨⟨l,h.local_le (h.component_le hl)⟩,
      h.constrained_normal_seed_le hn J hJ hq hout hf hl,rfl⟩
  have hML : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn
  have hs : conjugateSpanBy L M = L := le_antisymm
    (conjugateSpanBy_le le_rfl hML) (le_conjugateSpanBy _ _)
  have hmV : ⁅L,V⁆ = V := by
    rw [commutator_comm]
    exact (show V = ⁅V,L⁆ from hs ▸ h.module_commutator).symm
  have hVU := h.constrained_module_le_starV J hJ hq hout hf
  obtain ⟨d,hd⟩ := literal_star_section K R
  let X : Submodule (ZMod 2) (Additive (starV K R)) := d.imageSpace V
  let qK := C.subtype.comp (toStarImage K R)
  have hmX : subspaceCommutator (ρ.comp qK) X (L.subgroupOf K) = X := by
    rw [subspaceCommutator_comp_map,←original_subgroup_star_map hLK,
      ←subspaceCommutator_comp_map,←d.imageSpace_commutator L V
        (hLK.trans le_sup_left) hVU,hmV]
  have hXspace : X ≤ s.space.toSubmodule := by
    rw [s.space_eq]
    change X ≤ subspaceCommutator (ρ.comp O.subtype) ⊤ (C.subgroupOf O)
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCO]
    rw [←hmX,subspaceCommutator_comp_map]
    apply Submodule.span_mono
    rintro _ ⟨a,⟨k,hk,rfl⟩,v,_,rfl⟩
    exact ⟨qK k,(toStarImage K R k).property,v,Submodule.mem_top,rfl⟩
  let j : s.space.toSubmodule →ₗ[ZMod 2] Additive (starV K R) := s.space.toSubmodule.subtype
  let A : Submodule (ZMod 2) s.space.toSubmodule := X.comap j
  have hAX : A.map j = X := by
    rw [Submodule.map_comap_eq,Submodule.range_subtype,inf_eq_right.mpr hXspace]
  have hact (k : K) (w : s.space.toSubmodule) :
      (ρ.comp qK) k (j w) = j (σ (q k) w) := by
    change ρ (qK k) w.val =
      ρ (((e.symm (e (eC.symm (toStarImage K R k)))) : O) : StarQuotient K R) w.val
    rw [e.symm_apply_apply]
    rfl
  have hmA : subspaceCommutator σ A B = A := by
    apply Submodule.map_injective_of_injective s.space.toSubmodule.subtype_injective
    have hh := subspaceCommutator_map_embedding (ρ.comp qK) σ q j hact (L.subgroupOf K) A
    rw [hAX,hmX] at hh
    exact hh.symm.trans hAX.symm
  have hcoreR : L.pCoreIn 2 ≤ R := hs ▸ h.span_core_le_radical
  have hcorecomm : ⁅L.pCoreIn 2,V⁆ ≤ ⊥ := by
    apply commutator_le.mpr
    intro l hl v hv
    obtain ⟨z,hz,rfl⟩ := h.module_le_center_radical hv
    have hc : l * (z : G) = (z : G) * l :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨l,hcoreR hl⟩)
    exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr hc)
  have hcoreB : ((L.pCoreIn 2).subgroupOf K).map q = B.pCoreIn 2 :=
    h.constrained_normal_seed_core_image hn eA5 J hJ hq hout hf E
  have hfixA : A ≤ fixedSpace σ (B.pCoreIn 2) := by
    intro w hw b
    have hb : b.val ∈ ((L.pCoreIn 2).subgroupOf K).map q := hcoreB.symm ▸ b.property
    obtain ⟨k,hk,he⟩ := hb
    have hkw : (ρ.comp qK) k (j w) = j w :=
      d.fixed_on_imageSpace_of_commutator_le (L.pCoreIn 2) V hcorecomm
      ⟨k,mem_sup_left k.property⟩ hk (j w) hw
    have hh : j (σ (q k) w) = j w := (hact k w).symm.trans hkw
    have hh' : σ (q k) w = w := Subtype.ext hh
    exact (congrArg (fun z : D => σ z w) he.symm).trans hh'
  refine ⟨A,hfixA,hmA,?_⟩
  intro v
  let u : (starV K R).map S.subtype := ⟨v,hVU v.property⟩
  have huX : (d.coordinates u).toAdd ∈ X :=
    (d.mem_imageSpace_iff V _).mpr ⟨u,v.property,rfl⟩
  let w : s.space.toSubmodule := ⟨(d.coordinates u).toAdd,hXspace huX⟩
  refine ⟨w,huX,hd u,?_⟩
  intro hv g
  have hqsurj : Function.Surjective q := E.surjective.comp (toStarImage_surjective K R)
  obtain ⟨k,rfl⟩ := hqsurj g
  have hkw : (ρ.comp qK) k (j w) = j w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (((starRepresentation K R (π ⟨k,mem_sup_left k.property⟩) w.val).toMul : S) : G) = _
    rw [starRepresentation_apply]
    change (k : G) * (((w.val.toMul : starV K R) : S) : G) * (k : G)⁻¹ =
      (((w.val.toMul : starV K R) : S) : G)
    rw [show (((w.val.toMul : starV K R) : S) : G) = v from hd u]
    exact mul_inv_eq_of_eq_mul (hv k k.property)
  exact Subtype.ext ((hact k w).symm.trans hkw)

end CFSG.Quasithin.ChapterC.HypothesisC28
