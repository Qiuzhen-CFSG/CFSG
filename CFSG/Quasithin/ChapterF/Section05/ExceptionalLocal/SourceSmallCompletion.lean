module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.Transport
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionQuadrangle
/-!
# Applying the order-four criterion to the literal fixed endpoints

An ordinary graph-fixed endpoint element lying in the full marked overlap
already lies in the other ordinary fixed endpoint. Thus escape from the
intersection of the two fixed endpoints implies escape from the full overlap.
The resulting involutions pull back through the original embedding to the
faithful doubled completion, exactly as required by F.5.5(4) and F.4.26.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem Dendpoint_mem_other_of_middle (hi : Function.Injective i) (b : Bool) (x : G)
    (hx : x∈Dendpoint c i b) (hm : x∈(i.comp c.middle).range) :
    x∈Dendpoint c i (!b) := by
  have hxC := (Dendpoint_le_E c i b hx).2
  cases b with
  | false =>
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨w,hw⟩ := hm
    have hwleft : (Extension.amalgam 1 hn).left w=Source.pointInclusion a :=
      c.left_injective (hi hw)
    have hwval : w.val=SemidirectProduct.inl a.val := congrArg Subtype.val hwleft
    have haR : a.val∈planeParabolic 1 hn := by
      have hh : SemidirectProduct.inl a.val∈Extension.plane 1 hn := hwval ▸ ((Extension.amalgam 1 hn).right w).property
      exact (Extension.mem_plane 1 hn _).mp hh
    let q : planeParabolic 1 hn := ⟨a.val,haR⟩
    have hq : Source.planeInclusion q=(Extension.amalgam 1 hn).right w :=
      Subtype.ext hwval.symm
    have hmap : ordinaryMap c i true q=ordinaryMap c i false a := by
      change i (c.right (Source.planeInclusion q))=i (c.left (Source.pointInclusion a))
      rw [hq]
      have hc : c.middle w=c.right ((Extension.amalgam 1 hn).right w) :=
        DFunLike.congr_fun c.compatible w
      exact (congrArg i hc.symm).trans hw
    refine ⟨q,?_,hmap⟩
    change ordinaryInclusion true q∈centralizer ({modelGraph true} : Set (modelEndpoint true))
    apply mem_centralizer_singleton_iff.mpr
    apply endpointMap_injective c i hi true
    rw [map_mul,map_mul,endpointMap_graph]
    change ordinaryMap c i true q*Source.graphElement c i=Source.graphElement c i*ordinaryMap c i true q
    rw [hmap]
    exact mem_centralizer_singleton_iff.mp hxC
  | true =>
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨w,hw⟩ := hm
    have hwright : (Extension.amalgam 1 hn).right w=Source.planeInclusion a := by
      apply c.right_injective
      have hc : c.middle w=c.right ((Extension.amalgam 1 hn).right w) :=
        DFunLike.congr_fun c.compatible w
      exact hc.symm.trans (hi hw)
    have hwval : w.val=SemidirectProduct.inl a.val := congrArg Subtype.val hwright
    have haP : a.val∈pointParabolic 1 hn := by
      have hh : SemidirectProduct.inl a.val∈Extension.point 1 hn := hwval ▸ ((Extension.amalgam 1 hn).left w).property
      exact (Extension.mem_point 1 hn _).mp hh
    let q : pointParabolic 1 hn := ⟨a.val,haP⟩
    have hq : Source.pointInclusion q=(Extension.amalgam 1 hn).left w :=
      Subtype.ext hwval.symm
    have hmap : ordinaryMap c i false q=ordinaryMap c i true a := by
      change i (c.left (Source.pointInclusion q))=i (c.right (Source.planeInclusion a))
      rw [hq]
      exact hw
    refine ⟨q,?_,hmap⟩
    change ordinaryInclusion false q∈centralizer ({modelGraph false} : Set (modelEndpoint false))
    apply mem_centralizer_singleton_iff.mpr
    apply endpointMap_injective c i hi false
    rw [map_mul,map_mul,endpointMap_graph]
    change ordinaryMap c i false q*Source.graphElement c i=Source.graphElement c i*ordinaryMap c i false q
    rw [hmap]
    exact mem_centralizer_singleton_iff.mp hxC

theorem Dendpoint_not_mem_middle_of_not_intersection (hi : Function.Injective i)
    (b : Bool) (x : G) (hx : x∈Dendpoint c i b)
    (hout : x∉Dendpoint c i false⊓Dendpoint c i true) : x∉(i.comp c.middle).range := by
  intro hm
  have hh := Dendpoint_mem_other_of_middle c i hi b x hx hm
  cases b
  · exact hout ⟨hx,hh⟩
  · exact hout ⟨hh,hx⟩

/-- The literal fixed-endpoint witnesses pull back to the original completion. -/
theorem exists_completion_involutions_of_fixed_endpoints (hi : Function.Injective i)
    (s t : G) (hs : s∈Dendpoint c i false) (ht : t∈Dendpoint c i true)
    (hsout : s∉Dendpoint c i false⊓Dendpoint c i true)
    (htout : t∉Dendpoint c i false⊓Dendpoint c i true)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    ∃ a b : G0,a∈c.left.range ∧ b∈c.right.range ∧
      a∉c.middle.range ∧ b∉c.middle.range ∧ a^2=1 ∧ b^2=1 ∧ (a*b)^4=1 ∧ i a=s ∧ i b=t := by
  obtain ⟨a,ha⟩ := (Dendpoint_le_E c i false hs).1
  obtain ⟨b,hb⟩ := (Dendpoint_le_E c i true ht).1
  have ha' : i (c.left a)=s := ha
  have hb' : i (c.right b)=t := hb
  refine ⟨c.left a,c.right b,⟨a,rfl⟩,⟨b,rfl⟩,?_,?_,?_,?_,?_,ha',hb'⟩
  · intro hh
    apply Dendpoint_not_mem_middle_of_not_intersection c i hi false s hs hsout
    obtain ⟨w,hw⟩ := hh
    exact ⟨w,(congrArg i hw).trans ha'⟩
  · intro hh
    apply Dendpoint_not_mem_middle_of_not_intersection c i hi true t ht htout
    obtain ⟨w,hw⟩ := hh
    exact ⟨w,(congrArg i hw).trans hb'⟩
  · apply hi
    simpa only [map_pow,map_one,ha'] using hs2
  · apply hi
    simpa only [map_pow,map_one,hb'] using ht2
  · apply hi
    simpa only [map_pow,map_mul,map_one,ha',hb'] using hst

/-- Actual F.5.5 fixed-endpoint witnesses discharge the metric premise of F.4.26. -/
theorem source_quadrangle_metric_of_fixed_endpoints [Finite G] (hi : Function.Injective i)
    (s t : G) (hs : s∈Dendpoint c i false) (ht : t∈Dendpoint c i true)
    (hsout : s∉Dendpoint c i false⊓Dendpoint c i true)
    (htout : t∉Dendpoint c i false⊓Dendpoint c i true)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=4) :
    ∀v w,(SourceCompletion.UnitaryTwo.Extension.Completion.graph c).dist v w≤4 := by
  let : Finite G0 := Finite.of_injective i hi
  obtain ⟨a,b,ha,hb,hao,hbo,ha2,hb2,hab,_,_⟩ :=
    exists_completion_involutions_of_fixed_endpoints c i hi s t hs ht hsout htout
      (by rw [←hs2]; exact pow_orderOf_eq_one s)
      (by rw [←ht2]; exact pow_orderOf_eq_one t)
      (by rw [←hst]; exact pow_orderOf_eq_one (s*t))
  exact (SourceCompletion.UnitaryTwo.Extension.Completion.quadrangle_metric_of_involutions
    c a b ha hb hao hbo ha2 hb2 hab).2.1
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
