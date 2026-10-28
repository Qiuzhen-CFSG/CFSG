module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Fusion
public import Theory.GroupTheory.MinusExtraspecialOddCentralizer
public import Theory.GroupTheory.UniqueInvolutionSquareNormalizer

/-!
# The ambient centralizer of an outside terminal involution

In the retained S₅ branch, construct an involution j in the original T
outside the same selected K. Every order-four element in C_H(j) squares
to the original point z, and C_U(j) contains such an element. Hence the
normalizer of C_T(j) centralizes z and stays inside H. Its local Sylow
property promotes to C_T(j) being Sylow in C_G(j).

Its order is at most 32, whereas |T|=256. Therefore j is not conjugate to
z or any core involution, using the already proved fusion in U. Separation
from outside-core involutions of K and actual J₂/J₃ recognition remain
with the terminal-solvability owner.
Source: Aschbacher–Smith 14.2.17(1) and 14.3.15, printed pp.987 and 994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

/-- The outside S₅ involution has a globally Sylow centralizer and avoids
the ambient classes of every involution in the original core. -/
theorem source_single_a5_outside_centralizer_sylow_of_symmetric_five
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (eS : F.TerminalHdot ≃* Equiv.Perm (Fin 5)) :
    Nat.card T = 256 ∧
    ∃ z j : G, orderOf z = 2 ∧ F.H = centralizer ({z} : Set G) ∧
      j ∈ (T : Subgroup G) ∧ j ∉ K ∧ orderOf j = 2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({j} : Set G))
        (centralizer ({j} : Set G)) ∧
      Nat.card ↥((T : Subgroup G) ⊓ centralizer ({j} : Set G)) ≤ 32 ∧
      (∀ x ∈ (T : Subgroup G) ⊓ centralizer ({j} : Set G), orderOf x = 4 → x^2=z) ∧
      (∀ u ∈ F.U, orderOf u = 2 → ¬ IsConj j u) := by
  have hUH := source_single_a5_full_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  change F.U = (pCore 2 F.H).map F.H.subtype at hUH
  obtain ⟨eU⟩ := source_single_a5_minus_model_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,hres,_,hfit⟩ := source_single_a5_full_parabolic_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let eQ : pCore 2 F.H ≃* MinusExtraspecial.Model :=
    ((pCore 2 F.H).equivMapOfInjective F.H.subtype F.H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hUH.symm).trans eU)
  have hc : centralizer (pCore 2 F.H : Set F.H) ≤ pCore 2 F.H := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le _
  have hquot : Nat.card (F.H ⧸ pCore 2 F.H) = 120 := by
    rw [←hker]
    change Nat.card F.TerminalHdot = 120
    rw [Nat.card_congr eS.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hHcard : Nat.card F.H = 3840 := by
    rw [(pCore 2 F.H).card_eq_card_quotient_mul_card_subgroup,hquot,
      Nat.card_congr eQ.toEquiv,MinusExtraspecial.card_model]
  let TH : Sylow 2 F.H := T.subtype (F.invariant 1)
  have hTH : Nat.card TH = 256 := by
    rw [TH.card_eq_multiplicity,hHcard]
    decide +kernel
  have hTcard : Nat.card T = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe (F.invariant 1)).toEquiv).symm.trans hTH
  have hperf : IsPPerfect 2 (K.subgroupOf F.H) := by
    have hKperf : IsPPerfect 2 K := hres ▸ isPPerfect_embedded_pResidual 2 F.H
    exact hKperf.of_surjective (subgroupOfEquivOfLe hK.le_pointNormalizer).symm.toMonoidHom
      (subgroupOfEquivOfLe hK.le_pointNormalizer).symm.surjective
  obtain ⟨j,hj,hjK,hcore,hcent,⟨P,hP⟩,⟨q,hqj,hq2⟩,hsquare⟩ :=
    MinusExtraspecial.exists_outside_involution_with_unique_square
    (pCore 2 F.H) eQ hc hquot (K.subgroupOf F.H) hperf TH
  let jH : F.H := j
  have hjH : orderOf jH = 2 := (orderOf_coe j).trans hj
  have hlocal : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G))
      (F.H ⊓ centralizer ({(jH:G)} : Set G)) := by
    have hsH : Chapter1.IsSylowIn 2
        ((TH : Subgroup F.H) ⊓ centralizer ({jH} : Set F.H))
        (centralizer ({jH} : Set F.H)) := ⟨P,by rw [hP,subgroupOf_map_subtype]⟩
    have hTHmap : (TH : Subgroup F.H).map F.H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)
    have hsG := (Chapter1.IsSylowIn.map_iff F.H.subtype F.H.subtype_injective).mpr hsH
    simpa only [map_inf _ _ _ F.H.subtype_injective,hTHmap,Subgroup.map_subtype_centralizer_singleton,
      ←inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ F.H from F.invariant 1)] using hsG

  have hbound : Nat.card ↥((T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G)) ≤ 32 := by
    have hle : (T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G) ≤
        F.H ⊓ centralizer ({(jH:G)} : Set G) := inf_le_inf (F.invariant 1) le_rfl
    have hdvd : Nat.card ↥((T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G)) ∣ 96 :=
      (card_dvd_of_le hle).trans (by
        rwa [←Subgroup.map_subtype_centralizer_singleton F.H jH,
          card_map_of_injective F.H.subtype_injective])
    have hp : IsPGroup 2 ↥((T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G)) :=
      T.isPGroup'.to_le inf_le_left
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hd32 : Nat.card ↥((T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G)) ∣ 32 := by
      rw [hn] at hdvd ⊢
      exact ((show Nat.Coprime 2 3 from by decide).pow_left n).dvd_of_dvd_mul_right hdvd
    exact Nat.le_of_dvd (by decide) hd32

  let zQ : pCore 2 F.H := eQ.symm (MinusExtraspecial.quaternion MinusExtraspecial.z)
  let z0 : G := (zQ:F.H)
  have hzModel : orderOf (MinusExtraspecial.quaternion MinusExtraspecial.z)=2 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hz0 : orderOf z0=2 := (orderOf_coe (zQ:F.H)).trans
    ((orderOf_coe zQ).trans ((eQ.symm.orderOf_eq _).trans hzModel))
  have hzU : z0 ∈ F.U := hUH.symm ▸ mem_map_of_mem F.H.subtype zQ.property
  have hzcore : zQ ∈ center (pCore 2 F.H) := by
    apply mem_center_iff.mpr
    intro x
    apply eQ.injective
    simpa only [map_mul,zQ,eQ.apply_symm_apply] using
      mem_center_iff.mp ((MinusExtraspecial.mem_center_iff _).mpr (Or.inr rfl)) (eQ x)
  have hzZU : z0 ∈ F.ZU := by
    refine ⟨⟨z0,hzU⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro u
    have humem : (u:G) ∈ (pCore 2 F.H).map F.H.subtype := hUH ▸ u.property
    obtain ⟨uH,huH,hu⟩ := humem
    apply Subtype.ext
    change (u:G)*z0=z0*(u:G)
    rw [←hu]
    exact congrArg (fun x : pCore 2 F.H => ((x:F.H):G))
      (mem_center_iff.mp hzcore ⟨uH,huH⟩)
  have hzV : z0 ∈ F.Vi 1 :=
    (source_single_a5_center_eq_point_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd) ▸ hzZU
  have hZ : zpowers z0 = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr hzV)
    (by rw [Nat.card_zpowers,hz0]; simpa using (F.card 1 (by decide)).le)
  have hHz : F.H = centralizer ({z0} : Set G) := by
    change normalizer (F.Vi 1 : Set G) = _
    rw [←hZ]
    exact normalizer_zpowers_eq_centralizer_of_order_two z0 hz0
  let C := (T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G)
  have hroot2 : (((q:F.H):G))^2=z0 := congrArg Subtype.val hq2
  have hroot4 : orderOf (((q:F.H):G))=4 := by
    apply @orderOf_eq_prime_pow G _ _ 1 2 ⟨Nat.prime_two⟩
    · simpa only [pow_one,hroot2] using (orderOf_eq_prime_iff.mp hz0).2
    · change (((q:F.H):G))^4=1
      rw [show (4:Nat)=2*2 from rfl,pow_mul,hroot2]
      exact hz0 ▸ pow_orderOf_eq_one z0
  have hqT : ((q:F.H):G) ∈ (T : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := F.H)).le_sylow_of_normal TH q.property
  have hqC : ((q:F.H):G) ∈ C :=
    ⟨hqT,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hqj.eq)⟩
  have hsq : ∀ x ∈ C, orderOf x=4 → x^2=z0 := by
    intro x hx hx4
    let xH : F.H := ⟨x,F.invariant 1 hx.1⟩
    have hxH4 : xH^4=1 := Subtype.ext (hx4 ▸ pow_orderOf_eq_one x)
    have hxc : Commute xH jH := Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
    rcases hsquare xH hxc hxH4 with hs | hs
    · have he : x^2=1 := congrArg Subtype.val hs
      have hdvd := orderOf_dvd_of_pow_eq_one he
      rw [hx4] at hdvd
      norm_num at hdvd
    · exact congrArg Subtype.val hs
  have hindexLocal : ¬2 ∣ C.relIndex
      (centralizer ({z0} : Set G) ⊓ centralizer ({(jH:G)} : Set G)) := by
    rw [←hHz]
    obtain ⟨P0,hP0⟩ := hlocal
    have he : C.subgroupOf (F.H ⊓ centralizer ({(jH:G)} : Set G)) =
        (P0 : Subgroup _) := by
      change ((T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G)).subgroupOf _ = _
      rw [←hP0]
      exact comap_map_eq_self_of_injective (F.H ⊓ centralizer ({(jH:G)} : Set G)).subtype_injective _
    rw [relIndex,he]
    exact P0.not_dvd_index
  have hindex := not_two_dvd_centralizer_relIndex_of_unique_square C (jH:G) z0
    (T.isPGroup'.to_le inf_le_left) inf_le_right hindexLocal
    ⟨_,hqC,hroot4⟩ hsq
  have hglobal : Chapter1.IsSylowIn 2 C (centralizer ({(jH:G)} : Set G)) := by
    let P0 := ((T.isPGroup'.to_le (inf_le_left : C ≤ (T : Subgroup G))).comap_subtype
      (K := centralizer ({(jH:G)} : Set G))).toSylow hindex
    exact ⟨P0,map_subgroupOf_eq_of_le inf_le_right⟩
  have hnz : ¬IsConj (jH:G) z0 :=
    not_isConj_of_sylow_centralizer_card_lt (jH:G) z0 C (T : Subgroup G)
      (T.isPGroup'.to_le inf_le_left) T.isPGroup' inf_le_right
      (hHz ▸ F.invariant 1) hindex (by change Nat.card C ≤ 32 at hbound; omega)
  refine ⟨hTcard,z0,jH,hz0,hHz,j.property,hjK,(orderOf_coe jH).trans hjH,
    hglobal,hbound,hsq,?_⟩
  obtain ⟨z1,_,_,hfuse,_,_⟩ := source_single_a5_component_involution_fusion_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  intro u hu hu2 hju
  exact hnz (hju.trans ((hfuse u hu hu2).symm.trans (hfuse z0 hzU hz0)))

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
