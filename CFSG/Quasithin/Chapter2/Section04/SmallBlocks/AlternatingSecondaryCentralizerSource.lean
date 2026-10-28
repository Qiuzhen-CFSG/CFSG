module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingAffineInvolutionSource
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCensus
public import Theory.GroupTheory.NormalFourInvolutionCentralizerOrder
public import Theory.GroupTheory.ElementaryThompsonRelative
/-!
# The original secondary centralizer and its Sylow index

The order-nine subgroup of M acts transitively on the eighteen noncentral
involutions of its extraspecial core. Their centralizers have order 128.
The selected pair involution lies in the normal elementary center of J(S),
whose order is four; consequently its T-centralizer has index at most two.
The original marked packet therefore gives M_u=T_u and [T:T_u]=2, with
all coordinates and the central involution retained.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher

namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_noncentral_involution_centralizer_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)=⊥)
    (u : G)
    (huP : u ∈ (((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2))
    (hu2 : orderOf u=2)
    (huZ : u ∉ (center (((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2)).map
      (((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
        (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2).subtype) :
    Nat.card (M ⊓ centralizer ({u} : Set G) : Subgroup G)=128 := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let Q := pCore 2 M
  have hc := (d.single_alternating_maximal_core_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD).1
  change M.pCoreIn 2=P at hc
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let e : Q ≃* P := (Q.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hc)
  let hq := hp.map e.symm
  have hPM : P≤M := hc ▸ map_subtype_le _
  let uP : P := ⟨u,huP⟩
  let uQ : Q := e.symm uP
  have huQ : orderOf uQ=2 := (e.symm.orderOf_eq uP).trans
    ((orderOf_injective P.subtype P.subtype_injective uP).symm.trans hu2)
  have huQZ : uQ ∉ center Q := by
    intro hz
    have hzP : uP∈center P := by
      change uP ∈ Set.center P
      simpa only [uQ,e.apply_symm_apply] using (MulEquivClass.apply_mem_center_iff e).mpr hz
    exact huZ ⟨uP,hzP,rfl⟩
  have hself : centralizer (Q : Set M)≤Q := by
    intro x hx
    have hh : (x:G)∈M ⊓ centralizer (M.pCoreIn 2 : Set G) := by
      refine ⟨x.property,?_⟩
      rintro y ⟨a,ha,rfl⟩
      exact congrArg Subtype.val (hx a ha)
    obtain ⟨a,ha,hea⟩ := (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hh
    exact (M.subtype_injective hea) ▸ ha
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Sylow 3 M := Classical.choice inferInstance
  have hN : Nat.card N=9 := by
    rw [N.card_eq_multiplicity,d.single_alternating_maximal_card_of_centralizer_bot
      hG T hM hTM hu hST hsingle hA hD]
    decide +kernel
  have htrans := isConj_noncentral_involutions_of_order_nine Q hself
    hq.left hq.right hq.left_model hq.right_model hq.span hq.intersection_card hq.commute
    (N : Subgroup M) hN
  have horbit := hq.card_centralizer_mul_eighteen_of_transitive Q htrans uQ huQ huQZ
  have huval : ((uQ:Q):G)=u := by
    change ((e.symm uP:Q):G)=u
    have heval (a:Q) : (e a:G)=((a:M):G) := rfl
    rw [←heval,e.apply_symm_apply]
  have hmap : (centralizer ({(uQ:M)} : Set M)).map M.subtype=
      M ⊓ centralizer ({u}:Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.property,mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
      simpa only [coe_mul,huval,subtype_apply] using hh
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr (Subtype.ext ?_),rfl⟩
      simpa only [coe_mul,huval,subtype_apply] using mem_centralizer_singleton_iff.mp hc
  have hcard : Nat.card (centralizer ({(uQ:M)} : Set M))=
      Nat.card (M ⊓ centralizer ({u}:Set G) : Subgroup G) := by
    rw [←hmap,card_map_of_injective M.subtype_injective]
  rw [hcard,d.single_alternating_maximal_card_of_centralizer_bot
      hG T hM hTM hu hST hsingle hA hD] at horbit
  omega
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_secondary_centralizer_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)=⊥)
    (u : G) :
    let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
    let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    u∈P → orderOf u=2 → u∉(center P).map P.subtype →
    u∈(center R).map R.subtype → Nat.card (center R)=4 →
    IsElementaryAbelian 2 (center R) →
    M ⊓ centralizer ({u}:Set G)=(T : Subgroup G) ⊓ centralizer ({u}:Set G) ∧
      ((T : Subgroup G) ⊓ centralizer ({u}:Set G)).relIndex (T : Subgroup G)=2 := by
  intro P R huP hu2 huZ huR hRcard hRE
  let : IsElementaryAbelian 2 (center R) := hRE
  let Z := (center R).map R.subtype
  have hRT : R≤(T : Subgroup G) := (sSup_le fun _ h=>h.1).trans hST.le
  have hZT : Z≤(T : Subgroup G) := (map_subtype_le _).trans hRT
  have hJ : elementaryAbelianMaxJ (T : Subgroup G)=R :=
    (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).2.2
  have hnR : (T : Subgroup G)≤normalizer (R:Set G) := by
    rw [←hJ]
    exact (T : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hnZ : (T : Subgroup G)≤normalizer (Z:Set G) :=
    hnR.trans (normalizer_le_normalizer_characteristic_image R (center R))
  let W := Z.subgroupOf (T : Subgroup G)
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hZT).mpr hnZ
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hZT
  have hW : Nat.card W=4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZT).toEquiv,
      card_map_of_injective R.subtype_injective,hRcard]
  have hc : Nat.card (M ⊓ centralizer ({u}:Set G) : Subgroup G)=128 :=
    d.single_alternating_noncentral_involution_centralizer_card
      hG T hM hTM hu hST hsingle hA hD u huP hu2 huZ
  have hT : Nat.card (T : Subgroup G)=256 := by
    have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
    have hs : ((T.subtype hTM : Sylow 2 M) : Subgroup M)=
        (T : Subgroup G).subgroupOf M := rfl
    rw [←he,←hs,(T.subtype hTM).card_eq_multiplicity,
      d.single_alternating_maximal_card_of_centralizer_bot
        hG T hM hTM hu hST hsingle hA hD]
    decide +kernel
  exact Subgroup.centralizer_eq_sylow_of_normal_four_and_card
    (T : Subgroup G) M hTM T.isPGroup' W hW ⟨u,hZT huR⟩ huR hT hc
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_marked_secondary_centralizer
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)=⊥) :
    let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let J := elementaryAbelianMaxJ S
    let Z := (center P).map P.subtype
    ∃ eH : d.H ≃* BinaryFiveAffine.W,
      ((ChapterC.blockU d.block).map d.block.subtype).map eH.toMonoidHom=BinaryFiveAffine.vectorGroup ∧
      (d.S : Subgroup d.H).map eH.toMonoidHom=(BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W) ∧
      let u : G := (eH.symm BinaryFiveAffine.t : d.H)
      let s : G := (eH.symm BinaryFiveAffine.standardSwap : d.H)
      let z : G := (eH.symm BinaryFiveAffine.standardZ : d.H)
      u∈P ∧ orderOf u=2 ∧ u∈(center J).map J.subtype ∧ u∉Z ∧
      s∈S ∧ s∉J ∧ S ⊓ centralizer ({u}:Set G)=J ∧
      Z=zpowers z ∧ z=u*s*u*s⁻¹ ∧
      (center J).map J.subtype=zpowers u ⊔ zpowers z ∧
      Z≤(center (T:Subgroup G)).map (T:Subgroup G).subtype ∧
      M ⊓ centralizer ({u}:Set G)=(T:Subgroup G) ⊓ centralizer ({u}:Set G) ∧
      ((T:Subgroup G) ⊓ centralizer ({u}:Set G)).relIndex (T:Subgroup G)=2 := by
  obtain ⟨e,hU,hS,huU,hu2,huJ,huZ,hsS,hsJ,hCJ,hZ,hz,hJZ,hZT,huP,hJcard,hJE⟩ :=
    d.single_alternating_marked_involutions hG T hM hTM hu hST hsingle hA hD
  obtain ⟨hMu,hi⟩ := d.single_alternating_secondary_centralizer_of_marks
    hG T hM hTM hu hST hsingle hA hD (e.symm BinaryFiveAffine.t : d.H)
    huP hu2 huZ huJ hJcard hJE
  exact ⟨e,hU,hS,huP,hu2,huJ,huZ,hsS,hsJ,hCJ,hZ,hz,hJZ,hZT,hMu,hi⟩
end CFSG.Quasithin.Chapter2
