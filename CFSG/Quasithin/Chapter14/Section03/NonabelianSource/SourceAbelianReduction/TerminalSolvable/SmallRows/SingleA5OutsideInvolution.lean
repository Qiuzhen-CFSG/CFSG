module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Fusion
public import Theory.GroupTheory.MinusExtraspecialOddInvolutions

/-!
# Outside involutions in the original S₅ terminal branch

The literal full two-core is the original minus extraspecial U. Its intrinsic
five-point action is onto S₅ when the full terminal quotient is S₅. The norm
calculation constructs an involution in a transposition coset and Sylow conjugacy
places it in the original T with C_T(j) Sylow in C_H(j). Two-perfectness of the same selected K prevents
that involution from lying in K. Its centralizer in U has order eight and its
centralizer in H has order dividing 96. The same source branch has |T| = 256,
whereas |C_T(j)| ≤ 32.

This supplies the actual outside involution for 14.2.17(1), preserving the
original flag, quotient and component. The Sylow-centralizer structure and
ambient nonfusion, followed by J₂/J₃ recognition, remain to be established.
Source: Aschbacher–Smith 14.2.17 and 14.3.6,15, pp.986–987,991,994.
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

/-- The retained S₅ branch has an actual outside involution in the original
Sylow, with both core and local centralizer bounds on the same subgroups. -/
theorem source_single_a5_outside_involution_of_symmetric_five
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (eS : F.TerminalHdot ≃* Equiv.Perm (Fin 5)) :
    Nat.card T = 256 ∧
    ∃ j : G, j ∈ (T : Subgroup G) ∧ j ∉ K ∧ orderOf j = 2 ∧
      Nat.card ↥(F.U ⊓ centralizer ({j} : Set G)) = 8 ∧
      Nat.card ↥(F.H ⊓ centralizer ({j} : Set G)) ∣ 96 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({j} : Set G))
        (F.H ⊓ centralizer ({j} : Set G)) ∧
      Nat.card ↥((T : Subgroup G) ⊓ centralizer ({j} : Set G)) ≤ 32 := by
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
  obtain ⟨j,hj,hjK,hcore,hcent,P,hP⟩ := MinusExtraspecial.exists_involution_outside_twoPerfect
    (pCore 2 F.H) eQ hc hquot (K.subgroupOf F.H) hperf TH
  let jH : F.H := j
  have hjH : orderOf jH = 2 := (orderOf_coe j).trans hj
  refine ⟨hTcard,jH,j.property,hjK,(orderOf_coe jH).trans hjH,?_,?_,?_,?_⟩
  · have he : ((centralizer ({jH} : Set F.H)).subgroupOf (pCore 2 F.H)).map
        (F.H.subtype.comp (pCore 2 F.H).subtype) =
        F.U ⊓ centralizer ({(jH:G)} : Set G) := by
      rw [←map_map,subgroupOf_map_subtype,map_inf _ _ _ F.H.subtype_injective,
        Subgroup.map_subtype_centralizer_singleton,←hUH]
      rw [inf_right_comm,inf_eq_right.mpr F.U_le_H]
    rw [←he,←map_map,card_map_of_injective F.H.subtype_injective,
      card_map_of_injective (pCore 2 F.H).subtype_injective]
    exact hcore
  · rwa [←Subgroup.map_subtype_centralizer_singleton F.H jH,
      card_map_of_injective F.H.subtype_injective]

  · have hsH : Chapter1.IsSylowIn 2
        ((TH : Subgroup F.H) ⊓ centralizer ({jH} : Set F.H))
        (centralizer ({jH} : Set F.H)) := ⟨P,by rw [hP,subgroupOf_map_subtype]⟩
    have hTHmap : (TH : Subgroup F.H).map F.H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)
    have hsG := (Chapter1.IsSylowIn.map_iff F.H.subtype F.H.subtype_injective).mpr hsH
    simpa only [map_inf _ _ _ F.H.subtype_injective,hTHmap,Subgroup.map_subtype_centralizer_singleton,
      ←inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ F.H from F.invariant 1)] using hsG

  · have hle : (T : Subgroup G) ⊓ centralizer ({(jH:G)} : Set G) ≤
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

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
