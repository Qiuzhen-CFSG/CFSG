module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.PersistenceAtT
public import Theory.GroupTheory.GeneralizedFitting.InvariantFixedSeed
/-!
# The marked ordinary-component alternatives in original 2.5.19

The proved persistence theorem places K in C_G(t). The literal I.3.2 orbit
then supplies ordinary components of C_G(i). In its invariant branch,
conjugation by the same t is a genuine involution on the containing component,
and the original K is identified with the actual ordinary fixed component.
The pair branch retains the original odd-E orbit and both quotient maps.

All marks remain explicit; no containing-model list or fixed-component
identification is assumed. Source: Aschbacher–Smith 2.5.19, pp.560–561.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection

private theorem component_double_centralizer {G:Type*} [Group G]
    (K:Subgroup G) (t i:G) (htI:t∈centralizer ({i}:Set G))
    (hKi:K≤centralizer ({i}:Set G))
    (hKt:IsComponentIn K (centralizer ({t}:Set G))) :
    IsComponentIn (K.subgroupOf (centralizer ({i}:Set G)))
      (centralizer ({(⟨t,htI⟩:centralizer ({i}:Set G))}:Set (centralizer ({i}:Set G)))) := by
  let Gi:=centralizer ({i}:Set G)
  let tI:Gi:=⟨t,htI⟩
  let C:=centralizer ({tI}:Set Gi)
  let Ct:=centralizer ({t}:Set G)
  let D:=K.subgroupOf Gi
  have hDC:D≤C := by
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hKt.1 hk)
  let f:C→*Ct:=((Gi.subtype).comp C.subtype).codRestrict Ct (fun x=>by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))
  let e:(D.subgroupOf C)≃*K:=(subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hKi)
  refine ⟨hDC,hKt.2.1.comap f,?_⟩
  let : IsQuasisimple K:=hKt.quasisimple
  exact IsQuasisimple.of_mulEquiv e.symm

/-- The original source alternatives, retaining actual conjugation and fixed-component maps. -/
theorem source_marked_ordinary_pumpup {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t i:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (hi:orderOf i=2) (hiS:i∈(S:Subgroup H).map H.subtype)
    (hiK:i∈centralizer (K:Set G))
    (hbad:¬IsComponentIn K (centralizer ({i}:Set G))) :
    ∃htI:t∈centralizer ({i}:Set G),
      let Gi:=centralizer ({i}:Set G)
      let tI:Gi:=⟨t,htI⟩
      let D:=K.subgroupOf Gi
      let X:=componentOrbit D (oddELayer Gi)
      (IsComponent Gi X ∧ ∃a:MulAut X,orderOf a=2 ∧
        (∀x:X,((a x:Gi):G)=t*((x:Gi):G)*t⁻¹) ∧
        IsComponentIn (D.subgroupOf X) a.fixedSubgroup ∧
        Nonempty (K≃*((D.subgroupOf X).subgroupOf a.fixedSubgroup))) ∨
      ∃J:Subgroup Gi,IsComponent Gi J ∧ J≠J.map (MulAut.conj tI).toMonoidHom ∧
        X=J⊔J.map (MulAut.conj tI).toMonoidHom ∧
        Nonempty ((J⧸oddTwoCore J)≃*(K⧸oddTwoCore K)) := by
  have hKi:K≤centralizer ({i}:Set G):=fun k hk=>mem_centralizer_singleton_iff.mpr (hiK k hk)
  have hKt:=source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  obtain ⟨htI,hcases⟩:=source_ordinary_pumpup c hG hempty hgen hb hstar t i ht htC htZ hi hiS hiK
  let Gi:=centralizer ({i}:Set G)
  let tI:Gi:=⟨t,htI⟩
  let D:=K.subgroupOf Gi
  let X:=componentOrbit D (oddELayer Gi)
  refine ⟨htI,?_⟩
  rcases hcases with ⟨hX,hfix⟩|hpair
  · have hD:=component_double_centralizer K t i htI hKi hKt
    have hnot:¬IsComponent Gi D:=fun h=>hbad ⟨hKi,h⟩
    obtain ⟨a,ha,he,hB⟩:=invariant_component_fixed_seed tI ((Subgroup.orderOf_coe tI).symm.trans ht)
      hD hX (le_componentOrbit D (oddELayer Gi)) hfix hnot
    refine Or.inl ⟨hX,a,ha,fun x=>congrArg Subtype.val (he x),hB,?_⟩
    exact ⟨((subgroupOfEquivOfLe hB.1).trans
      ((subgroupOfEquivOfLe (le_componentOrbit D (oddELayer Gi))).trans
        (subgroupOfEquivOfLe hKi))).symm⟩
  · exact Or.inr hpair
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
