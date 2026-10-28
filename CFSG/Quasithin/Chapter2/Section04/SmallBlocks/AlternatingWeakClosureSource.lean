module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullCentralizerSource
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit
public import Theory.Frattini.BinarySquares
/-!
# Weak closure of the central involution in the original extraspecial core

The order-nine subgroup of M is transitive on the eighteen noncentral
involutions of its quaternion central product core P. The selected natural
pair involution u does not fuse with the central involution z. Thus every
ambient conjugate of z in P is central, and the center of P has order two.
Every premise is discharged by the original marked single-A5 source.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/
public section
open Subgroup Stellmacher
namespace Subgroup

private theorem center_involution_fusion_eq_of_noncentral_transitive
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (hcard : Nat.card (center P)=2)
    (u z : G)
    (hzZ:z∈(center P).map P.subtype) (hz2:orderOf z=2)
    (hsep:¬IsConj u z)
    (htrans:∀x∈P, orderOf x=2 → x∉(center P).map P.subtype → IsConj u x) :
    ∀x∈P, IsConj z x → x=z := by
  intro x hx hzx
  have hx2 : orderOf x=2 := by
    obtain ⟨c,hc⟩ := hzx
    exact (SemiconjBy.orderOf_eq (c:G) hc).symm.trans hz2
  by_cases hxZ:x∈(center P).map P.subtype
  · let Z := (center P).map P.subtype
    have hc : Nat.card Z=2 := by rw [card_map_of_injective P.subtype_injective,hcard]
    obtain ⟨unique,_,hunique⟩ := (Nat.card_eq_two_iff' (1:Z)).mp hc
    have hn (v:G) (hv:orderOf v=2) : v≠1 := by intro hh;rw[hh,orderOf_one] at hv;omega
    have he : (⟨x,hxZ⟩:Z)=(⟨z,hzZ⟩:Z) :=
      (hunique _ (fun hh=>hn x hx2 (congrArg Subtype.val hh))).trans
        (hunique _ (fun hh=>hn z hz2 (congrArg Subtype.val hh))).symm
    exact congrArg Subtype.val he
  · exact (hsep ((htrans x hx hx2 hxZ).trans hzx.symm)).elim
end Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_noncentral_involutions_isConj
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
      ∀x∈P, orderOf x=2 → x∉(center P).map P.subtype → IsConj u x := by
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
  have hhG := M.subtype.map_isConj hh
  change IsConj (((e.symm uP:Q):M):G) (((e.symm xP:Q):M):G) at hhG
  rw [hval,hval] at hhG
  exact hhG

theorem MinimalBlockSetup.single_alternating_center_weak_closed_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype < (T:Subgroup G))
    (hsingle:d.L0=d.block)
    (hA:ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD:(T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥)
    (u z:G) :
    let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
    u∈P → orderOf u=2 → u∉(center P).map P.subtype →
    z∈(center P).map P.subtype → orderOf z=2 → ¬IsConj u z →
    ∀x∈P, IsConj z x → x=z := by
  intro P huP hu2 huZ hzZ hz2 hsep
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  exact center_involution_fusion_eq_of_noncentral_transitive P hp.center_card
    u z hzZ hz2 hsep
    (d.single_alternating_noncentral_involutions_isConj hG T hM hTM hu hST hsingle hA hD
      u huP hu2 huZ)
end CFSG.Quasithin.Chapter2
