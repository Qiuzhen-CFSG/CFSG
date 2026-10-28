module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCoreIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoFixedLine
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineCosts
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelLines
public import Theory.GroupTheory.ThreeStepChainCentralizerTwoCore

/-!
# The original order-two partner puts the full module in its two-core

The canonical kernel inside the original normal closure of V stabilizes
all three layers of the actual chain 1 ≤ D ≤ F ≤ O2(Mc). Its two-residual
therefore centralizes O2(Mc), so the entire kernel intersection lies in
O2(Mc). Consequently V intersects its canonical action kernel in exactly E.
The same canonical V-image would have order sixteen, contradicting the
original support-image bound of four. This closes both cases at once without
lifting a quotient normalizer or discarding the full-action kernel.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- In the order-two partner case the unchanged full V lies in the original partner core. -/
theorem PreparedChosenModule.decomposable_five_partner_two_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      V ≤ Mc.pCoreIn 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let Q := Mc.pCoreIn 2
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let N := conjugateSpanBy V Mc
  let B := K ⊓ N
  by_contra hVQ
  obtain ⟨hCMc,hCQ,_,_,hself,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨hUc,hMc,_,_,_⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hMcC : Mc = C := hMc.trans (congrArg (fun Z : Subgroup G => centralizer (Z : Set G)) hUc.symm)
  have hselfQ : Mc ⊓ centralizer (Q : Set G) ≤ Q := by
    have hs : C ⊓ centralizer (Q : Set G) ≤ Q := by
      simpa only [hCQ] using hself
    exact (inf_le_inf_right _ hMcC.le).trans hs
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  obtain ⟨_,hFQ,hEF,hVQcomm,_,_⟩ := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨hDF,_,hDC,hnD,he,ρ,dF,_,hker,hcard,_,hoff,_⟩ :=
    (h.decomposable_five_partner_two_core_or_canonical_action hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  let : IsElementaryAbelian 2 F := he
  have hnQ : Mc ≤ normalizer (Q : Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hnF : Mc ≤ normalizer (F : Set G) := dF.normalized
  have hNMc : N ≤ Mc := conjugateSpanBy_le_self hVMc
  have hVN : V ≤ N := le_conjugateSpanBy V Mc
  have hND : N ≤ centralizer (D : Set G) := conjugateSpanBy_le
    (le_centralizer_iff.mp hDC) (hnD.trans (normalizer_le_normalizer_centralizer D))
  have hNQ : ⁅N,Q⁆ ≤ F := by
    have hnP : Mc ≤ normalizer (commutatorPreimage Mc Q F : Set G) :=
      commutatorPreimage_normalized Mc Q F Mc hnF Mc.le_normalizer hnQ hnF
    have hNP : N ≤ commutatorPreimage Mc Q F :=
      conjugateSpanBy_le (le_commutatorPreimage hVMc (hVQcomm.trans hEF)) hnP
    exact (commutator_mono hNP le_rfl).trans
      (commutator_commutatorPreimage_le Mc Q F hnF)
  have hBQ : B ≤ Q := le_twoCore_of_relative_three_step_chain Mc Q F D B
    (pCoreIn_le 2 Mc) dF.section_le (hDF.le.trans dF.section_le)
    (inf_le_right.trans hNMc) hnQ hnF hnD (isPGroup_pCoreIn 2 Mc) hselfQ
    (inf_le_right.trans hND)
    ((commutator_mono inf_le_left le_rfl).trans
      (commutator_commutatorPreimage_le Mc F D hnD))
    ((commutator_mono inf_le_right le_rfl).trans hNQ)
  obtain ⟨hVCF,hVQeq,_⟩ := (h.decomposable_five_partner_two_core_intersection
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hVK : V ⊓ K = E := by
    apply le_antisymm
    · intro v hv
      apply hVQeq.le
      exact ⟨hv.1,hBQ ⟨hv.2,hVN hv.1⟩⟩
    · have hEK : E ≤ K := le_commutatorPreimage (hEF.trans dF.section_le)
        ((commutator_eq_bot_iff_le_centralizer.mpr
          (hVCF.symm.le.trans inf_le_right)).le.trans bot_le)
      exact le_inf inf_le_left hEK
  have hVcard : Nat.card V = 256 := by
    rw [←s.complement,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _)))).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr s.disjoint),s.support_card,s.support_card]
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hAc : Nat.card A = 16 := by
    have hh := relIndex_mul_card_of_le (show V ⊓ K ≤ V from inf_le_left)
    rw [inf_relIndex_left,hVK,s.fixed_card,hVcard] at hh
    change Nat.card A = K.relIndex V at hcard
    omega
  have hline := ((h.decomposable_five_partner_two_core_or_kernel_lines
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ).1
  obtain ⟨_,_,_,_,_,_,_,_,_,hsmall,_⟩ :=
    ((h.decomposable_five_partner_two_line_actor_bounds hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hline
  change Nat.card A ≤ 4 at hsmall
  omega

end CFSG.Quasithin.Chapter15.Section01
