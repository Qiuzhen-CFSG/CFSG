module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterFusionSplit
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterFusionTransport
/-!
# Original fusion for the PSL₃(3) shadow

The source crossing constructs one complement A and its exact inner
marking. Its two crossing equations, the single inner involution class
and the single outer involution class give the full source fusion:
every involution in A is conjugate to z, and every involution in H−A
is conjugate to t. The conclusion keeps C_G(t)=H and the nonfusion of
t and z, ready for the elementary-sixteen normalizer contradiction.
All inputs are the original source tuple and selected largest local pair.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_fusion
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S:Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U≤(S:Subgroup H).map H.subtype)
    (eK : K≃*Matrix.PSL3Three.PSL) :
    z∈K ∧ ∃ t : G, orderOf t=2 ∧ centralizer ({t}:Set G)=H ∧ ¬IsConj t z ∧
      ∃ A : Subgroup G, K≤A ∧ ∃ eA:A≃*MulAut Matrix.PSL3Three.PSL,
      K.subgroupOf A=(MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap eA.toMonoidHom ∧
      H=zpowers t⊔A ∧ Disjoint (zpowers t) A ∧ zpowers t≤centralizer (A:Set G) ∧
      (∀ v∈A,orderOf v=2 → IsConj z v) ∧
      (∀ v∈H,v∉A → orderOf v=2 → IsConj t v) := by
  obtain ⟨hzK,t,a,x,ht,hCt,htz,haK,hao,htx,A,hKA,eA,hinner,hspan,hdis,hcomm,f,hfe,hfK⟩ :=
    linear_three_source_fusion_split c hG hempty hgen hb hp hUS eK
  obtain ⟨hin,hout⟩ := linear_three_outer_fusion_of_crossing hKA eK eA hinner.symm
    t ht hspan hdis hcomm (⟨a,haK⟩:K) (⟨z,hzK⟩:K)
    (by simpa only [Subgroup.orderOf_mk] using hao)
    (by simpa only [Subgroup.orderOf_mk] using c.involution) f hfK x htx hfe.symm
  exact ⟨hzK,t,ht,hCt,htz,A,hKA,eA,hinner,hspan,hdis,hcomm,
    fun v hv ho => (hin v hv ho).symm,fun v hv hn ho => (hout v hv hn ho).symm⟩
end CFSG.Quasithin.Chapter2.Section05
