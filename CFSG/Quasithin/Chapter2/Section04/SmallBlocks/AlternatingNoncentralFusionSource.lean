module
public import Theory.GroupTheory.OutsideCentralizerFusion
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingWeakClosureSource
/-!
# Marked conjugators for the noncentral involutions of the original core

The order-nine action on P supplies conjugators in M, retaining their ambient
membership. These are used to move the involution fixed by the outer-square
representative to the original pair involution u. Normality of the residual
subgroup then preserves the outside-S marking.

Source: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_noncentral_involutions_conjugator
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype < (T:Subgroup G))
    (hsingle:d.L0=d.block)
    (hA:ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD:(T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥) :
    let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
    ∀u∈P, orderOf u=2 → u∉(center P).map P.subtype →
      ∀x∈P, orderOf x=2 → x∉(center P).map P.subtype → ∃m∈M, m*u*m⁻¹=x := by
  intro P u huP hu2 huZ x hxP hx2 hxZ
  let Q := pCore 2 M
  have hc := (d.single_alternating_maximal_core_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD).1
  change M.pCoreIn 2=P at hc
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let e : Q ≃* P := (Q.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hc)
  let hq := hp.map e.symm
  have hself : centralizer (Q:Set M)≤Q := by
    intro a ha
    have hh : (a:G)∈M ⊓ centralizer (M.pCoreIn 2:Set G) := by
      refine ⟨a.property,?_⟩
      rintro y ⟨b,hb,rfl⟩
      exact congrArg Subtype.val (ha b hb)
    obtain ⟨b,hb,heb⟩ := (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hh
    exact (M.subtype_injective heb) ▸ hb
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Sylow 3 M := Classical.choice inferInstance
  have hN : Nat.card N=9 := by
    rw [N.card_eq_multiplicity,d.single_alternating_maximal_card_of_centralizer_bot
      hG T hM hTM hu hST hsingle hA hD]
    decide +kernel
  let uP : P := ⟨u,huP⟩
  let xP : P := ⟨x,hxP⟩
  have ho (v:P) (hv:orderOf (v:G)=2) : orderOf (e.symm v)=2 :=
    (e.symm.orderOf_eq v).trans ((orderOf_injective P.subtype P.subtype_injective v).symm.trans hv)
  have hn (v:P) (hv:(v:G)∉(center P).map P.subtype) : e.symm v∉center Q := by
    intro hz
    have hzP : v∈center P := by
      change v∈Set.center P
      simpa only [e.apply_symm_apply] using (MulEquivClass.apply_mem_center_iff e).mpr hz
    exact hv ⟨v,hzP,rfl⟩
  have hh := isConj_noncentral_involutions_of_order_nine Q hself
    hq.left hq.right hq.left_model hq.right_model hq.span hq.intersection_card hq.commute
    (N:Subgroup M) hN (e.symm uP) (e.symm xP) (ho uP hu2) (hn uP huZ)
      (ho xP hx2) (hn xP hxZ)
  have hval (v:P) : ((e.symm v:Q):G)=(v:G) := by
    have heval (a:Q) : (e a:G)=((a:M):G) := rfl
    rw [←heval,e.apply_symm_apply]
  obtain ⟨m,hm⟩ := isConj_iff.mp hh
  refine ⟨m,m.property,?_⟩
  have hhG := congrArg Subtype.val hm
  change (m:G)*(((e.symm uP:Q):M):G)*(m:G)⁻¹=(((e.symm xP:Q):M):G) at hhG
  rwa [hval,hval] at hhG

end CFSG.Quasithin.Chapter2
