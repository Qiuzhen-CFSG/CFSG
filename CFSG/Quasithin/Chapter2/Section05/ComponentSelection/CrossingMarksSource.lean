module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CenterSource
public import Theory.GroupTheory.CentralFourNormalizerAction
/-! # Original normalizer index and crossing on the central marks
The actual Sylow of C_G(t) supplied by source 2.5.11 makes C_T(t)=S.
The proved central four-group action therefore gives |N_T(S):S|=2 and
 t^x=tz for every original outside normalizer element, as in 2.5.13(1).
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.ambient_centralizer_core_involution
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype)) :
    (c.T:Subgroup G)⊓centralizer ({t}:Set G)=(S:Subgroup H).map H.subtype := by
  obtain ⟨_,_,⟨P,hP⟩,_,_⟩:=MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  let C:=centralizer ({t}:Set G)
  have hPQ:(P:Subgroup C)≤(c.T:Subgroup G).subgroupOf C:=by
    intro a ha
    exact c.sylow_lt.le (hP ▸ mem_map_of_mem C.subtype ha)
  have he:P.toSubgroup=(c.T:Subgroup G).subgroupOf C:=
    (P.is_maximal' c.T.isPGroup'.comap_subtype hPQ).symm
  have hm:=congrArg (Subgroup.map C.subtype) he
  rw [hP,subgroupOf_map_subtype] at hm
  exact hm.symm

theorem MathieuSourceSetup.source_crossing_on_center
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (hE:IsKleinFour (centerIn ((S:Subgroup H).map H.subtype))) :
    ((S:Subgroup H).map H.subtype).relIndex
        ((c.T:Subgroup G)⊓normalizer ((S:Subgroup H).map H.subtype:Set G))=2 ∧
      ∀x:G,x∈c.T→x∈normalizer ((S:Subgroup H).map H.subtype:Set G)→
        x∉(S:Subgroup H).map H.subtype→x⁻¹*t*x=t*z := by
  let :=hE
  have hzT:z∈centerIn (c.T:Subgroup G):=by
    simpa only [centerIn_eq_map_center] using c.mem_center
  have htz:t≠z:=by
    intro he
    have hc:=MathieuSourceSetup.central_core_involution_not_mem_center_ambient c hgen t ht htC htZ
    exact hc (he.symm ▸ hzT)
  have hCt:=MathieuSourceSetup.ambient_centralizer_core_involution c hgen t ht htC htZ
  exact ⟨normalizer_index_two_of_central_four _ _ c.T.isPGroup' c.sylow_lt t z ht c.involution htZ hzT htz hCt,
    fun x hxT hxN hxS=>normalizer_crossing_on_central_four _ _ c.sylow_lt.le t z ht c.involution htZ hzT htz hCt x hxT hxN hxS⟩

/-- Source 2.5.13(2) in its stronger elementwise fixed-projection form. -/
theorem MathieuSourceSetup.source_fixed_projection
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (hE:IsKleinFour (centerIn ((S:Subgroup H).map H.subtype)))
    (x:G) (hxT:x∈c.T) (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hxS:x∉(S:Subgroup H).map H.subtype)
    (k:G) (hk:orderOf k=2) (hkZ:k∈centerIn ((S:Subgroup H).map H.subtype))
    (hfix:x⁻¹*k*x=k) : k=z := by
  let :=hE
  have hzT:z∈centerIn (c.T:Subgroup G):=by
    simpa only [centerIn_eq_map_center] using c.mem_center
  have htz:t≠z:=fun he=>MathieuSourceSetup.central_core_involution_not_mem_center_ambient
    c hgen t ht htC htZ (he.symm ▸ hzT)
  exact fixed_mark_of_central_four_crossing _ _ c.sylow_lt.le t z ht c.involution htZ hzT htz
    (MathieuSourceSetup.ambient_centralizer_core_involution c hgen t ht htC htZ)
    x hxT hxN hxS k hk hkZ hfix

/-- Source 2.5.13(3): fusion of the product selects the original projection. -/
theorem MathieuSourceSetup.source_fused_projection
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (hE:IsKleinFour (centerIn ((S:Subgroup H).map H.subtype)))
    (k:G) (hk:orderOf k=2) (hkZ:k∈centerIn ((S:Subgroup H).map H.subtype))
    (hkC:k∉twoCore H) (hf:IsConj t (t*k)) : k=z := by
  let Y:=(S:Subgroup H).map H.subtype
  let :=hE
  have hzT:z∈centerIn (c.T:Subgroup G):=by
    simpa only [centerIn_eq_map_center] using c.mem_center
  have hzZ:z∈centerIn Y:=⟨c.center_le c.mem_center,fun a ha=>hzT.2 a (c.sylow_lt.le ha)⟩
  have htz:t≠z:=fun he=>MathieuSourceSetup.central_core_involution_not_mem_center_ambient
    c hgen t ht htC htZ (he.symm ▸ hzT)
  have ht1:t≠1:=by intro h;rw [h,orderOf_one] at ht;omega
  have hz1:z≠1:=by intro h;have hz:=c.involution;rw [h,orderOf_one] at hz;omega
  have hk1:k≠1:=by intro h;rw [h,orderOf_one] at hk;omega
  have hkt:k≠t:=fun he=>hkC (he.symm ▸ htC)
  by_contra hkz
  have he:=IsKleinFour.eq_mul_of_ne_all
    (x:=(⟨t,htZ⟩:centerIn Y)) (y:=(⟨z,hzZ⟩:centerIn Y)) (z:=(⟨k,hkZ⟩:centerIn Y))
    (fun h=>ht1 (congrArg Subtype.val h)) (fun h=>hz1 (congrArg Subtype.val h))
    (fun h=>htz (congrArg Subtype.val h)) (fun h=>hk1 (congrArg Subtype.val h))
    (fun h=>hkt (congrArg Subtype.val h)) (fun h=>hkz (congrArg Subtype.val h))
  have hke:k=t*z:=congrArg Subtype.val he
  have htt:t*t=1:=by
    have hh:t^2=1:=by rw [←ht];exact pow_orderOf_eq_one t
    simpa only [pow_two] using hh
  have hez:t*k=z:=by rw [hke,←mul_assoc,htt,one_mul]
  exact (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).2.2.2.2 (hez ▸ hf)

/-- The original normalizer index, with every central-mark premise discharged. -/
theorem MathieuSourceSetup.source_normalizer_index_two
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel L) :
    ((S:Subgroup H).map H.subtype).relIndex
      ((c.T:Subgroup G)⊓normalizer ((S:Subgroup H).map H.subtype:Set G))=2 := by
  obtain ⟨t,k,ht,_,htC,hcore,_,_,_,hE,_⟩:=MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ:t∈centerIn ((S:Subgroup H).map H.subtype):=by
    have hh:t∈centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H:=hcore.symm ▸ mem_zpowers t
    exact hh.1
  exact (MathieuSourceSetup.source_crossing_on_center c hgen t ht htC htZ hE).1

/-- Construct the crossing involution and its exact original conjugation formula. -/
theorem MathieuSourceSetup.source_crossing_involution
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel L) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧
      centerIn ((S:Subgroup H).map H.subtype)=zpowers t⊔zpowers z ∧
      ∀x:G,x∈c.T→x∈normalizer ((S:Subgroup H).map H.subtype:Set G)→
        x∉(S:Subgroup H).map H.subtype→x⁻¹*t*x=t*z := by
  obtain ⟨t,k,ht,_,htC,hcore,_,hspan,_,hE,_⟩:=MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ:t∈centerIn ((S:Subgroup H).map H.subtype):=by
    have hh:t∈centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H:=hcore.symm ▸ mem_zpowers t
    exact hh.1
  exact ⟨t,ht,htC,hspan,(MathieuSourceSetup.source_crossing_on_center c hgen t ht htC htZ hE).2⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
