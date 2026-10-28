module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5OutsideCentralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5FourCycleLift
public import Theory.GroupTheory.UniqueInvolutionSquareSeparation

/-!
# Excluding the symmetric-five terminal centralizer

Thompson transfer puts the previously constructed outside involution j into
the same selected K. It cannot fuse into U. A four-cycle lift in H has order
four and square in K outside U; fusion inside K therefore makes j conjugate
to that square. The unique-square property of the globally Sylow C_T(j)
contradicts this. Thus H/O₂(H) is A₅, H=K, and the literal involution
centralizer gives the genuine J₂/J₃ local type.

The equality H=K is proved from orders after excluding S₅; normalization by
T is never used to assert T≤K. Actual ambient J₂/J₃ recognition remains
with the terminal-solvability owner.
Source: Aschbacher–Smith 14.2.17(1),14.3.6(1),14.3.15, pp.987,991,994.
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

/-- The full S₅ terminal quotient is impossible: its odd involution has a
unique central square, while its conjugate in K has an order-four root. -/
theorem source_single_a5_not_symmetric_five_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (eS : F.TerminalHdot ≃* Equiv.Perm (Fin 5)) : False := by
  obtain ⟨hTc,z,j,hz,hHz,hjT,hjK,hj,⟨P,hP⟩,hbound,hsq,hno⟩ :=
    source_single_a5_outside_centralizer_sylow_of_symmetric_five hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd eS
  obtain ⟨u,huo,hju⟩ := source_single_a5_involutions_into_component_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd j hj
  have huU : (u:G) ∉ F.U := fun hh => hno u hh ((orderOf_coe u).trans huo) hju
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
  have hquot : Nat.card (F.H ⧸ pCore 2 F.H)=120 := by
    rw [←hker]
    change Nat.card F.TerminalHdot=120
    rw [Nat.card_congr eS.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  let uH : F.H := ⟨u,hK.le_pointNormalizer u.property⟩
  have huH : orderOf uH=2 := (orderOf_coe uH).symm.trans ((orderOf_coe u).trans huo)
  have huQ : uH ∉ pCore 2 F.H := fun hh => huU (hUH.symm ▸ mem_map_of_mem F.H.subtype hh)
  have hperfK : IsPPerfect 2 K := hres ▸ isPPerfect_embedded_pResidual 2 F.H
  have hperf : IsPPerfect 2 (K.subgroupOf F.H) := hperfK.of_surjective
    (subgroupOfEquivOfLe hK.le_pointNormalizer).symm.toMonoidHom
    (subgroupOfEquivOfLe hK.le_pointNormalizer).symm.surjective
  obtain ⟨_,hidx,_⟩ := source_single_a5_component_index_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let uKH : K.subgroupOf F.H := ⟨uH,u.property⟩
  obtain ⟨r,hr,hrK,hrQ⟩ := MinusExtraspecial.exists_outside_square
    (pCore 2 F.H) eQ hc hquot (K.subgroupOf F.H) hperf hidx uKH
    ((orderOf_coe uKH).symm.trans huH) huQ
  let t : K := ⟨(r:G)^2,hrK⟩
  have ht : orderOf t=2 := by
    rw [←orderOf_coe]
    have hh : orderOf (r^2)=2 := by
      rw [orderOf_pow,hr]
      decide
    exact (orderOf_coe (r^2)).trans hh
  have htU : (t:G) ∉ F.U := by
    intro hh
    have hh' : (r:G)^2 ∈ (pCore 2 F.H).map F.H.subtype := hUH ▸ hh
    obtain ⟨q,hq,hqe⟩ := hh'
    exact hrQ ((show q=r^2 from Subtype.ext hqe) ▸ hq)
  obtain ⟨_,_,_,_,hfuse,_⟩ := source_single_a5_component_involution_fusion_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hjt : IsConj j (t:G) := hju.trans (K.subtype.map_isConj (hfuse u t huo ht huU htU))
  have hjz : j ≠ z := by
    intro he
    rw [he,←hHz,inf_eq_left.mpr (show (T:Subgroup G)≤F.H from F.invariant 1),hTc] at hbound
    omega
  have hsquare : ∀ x : P, orderOf x=4 → ((x:centralizer ({j}:Set G)):G)^2=z := by
    intro x hx
    apply hsq
    · rw [←hP]
      exact mem_map_of_mem _ x.property
    · exact (orderOf_coe (x:centralizer ({j}:Set G))).trans ((orderOf_coe x).trans hx)
  exact not_isConj_square_of_unique_square j z P hsquare hjz (r:G)
    ((orderOf_coe r).trans hr) hjt.symm

/-- The normalized component is the full involution centralizer and gives
the genuine J₂/J₃ local type; the symmetric-five alternative is eliminated. -/
theorem source_single_a5_janko_type_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.H=K ∧ Nonempty (F.TerminalHdot ≃* alternatingGroup (Fin 5)) ∧
    ∃ z : G, orderOf z=2 ∧ F.H=centralizer ({z}:Set G) ∧
      Janko23.ambientCore z=F.U ∧ Janko23.HTypeAt z ∧
      (Janko23.J2Type G ∨ Janko23.J3Type G) := by
  have hA : Nonempty (F.TerminalHdot ≃* alternatingGroup (Fin 5)) := by
    rcases source_single_a5_whole_group_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd with ha | hs
    · exact ha
    · exact (source_single_a5_not_symmetric_five_of_four hG T hempty hM hu hmany
        hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd hs.some).elim
  have hdotcard : Nat.card F.TerminalHdot=60 := by
    rw [Nat.card_congr hA.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨hfull,z,hz,hHz,hamb,hecore,hreturn,hloc⟩ :=
    source_single_a5_involution_centralizer_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hfit⟩ := source_single_a5_full_parabolic_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hQcard : Nat.card (pCore 2 F.H)=32 := by
    have hc := Nat.card_congr hecore.some.toEquiv
    change Nat.card (generalizedFitting (centralizer ({z}:Set G))) = _ at hc
    rw [←hHz,hfit,MinusExtraspecial.card_model] at hc
    exact hc
  have hHcard : Nat.card F.H=1920 := by
    rw [(pCore 2 F.H).card_eq_card_quotient_mul_card_subgroup,hQcard,←hker]
    change Nat.card F.TerminalHdot*32=1920
    rw [hdotcard]
  have hKcard := (source_single_a5_component_index_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd).1
  have hHK : F.H=K := (eq_of_le_of_card_ge hK.le_pointNormalizer (by omega)).symm
  refine ⟨hHK,hA,z,hz,hHz,hamb,?_⟩
  rcases hloc with hloc | hs
  · exact hloc
  · have hc := Nat.card_congr hs.some.toEquiv
    change Nat.card ((centralizer ({z}:Set G)) ⧸ generalizedFitting
      (centralizer ({z}:Set G))) = Nat.card (Equiv.Perm (Fin 5)) at hc
    rw [←hHz,hfit,←hker] at hc
    change Nat.card F.TerminalHdot=Nat.card (Equiv.Perm (Fin 5)) at hc
    rw [hdotcard,Nat.card_eq_fintype_card,Fintype.card_perm] at hc
    norm_num [Nat.factorial] at hc

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
