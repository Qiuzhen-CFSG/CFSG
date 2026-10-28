module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFifteen
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Movement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Quotient

/-!
# An actual reduced section in the original order-fifteen branch

The literal marked residual of order fifteen first identifies the partner
module with the full Thompson fixed subgroup E. The original chosen module
then lies in the partner core. Its actual centralizer span H is elementary
and lies in both original cores. Thompson movement survives on H/E, whose
literal image in C_G(E)/E is reduced.

This gives a genuine original section for the remaining order-fifteen
argument. It does not assert a model classification or an exclusion.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original order-fifteen source produces its literal common-core span
and a reduced quotient section still moved by the original Thompson group. -/
theorem PreparedChosenModule.decomposable_fifteen_span_section
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z₁ : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 15 →
      let E := thompsonFixed T V
      let C := centralizer (E : Set G)
      let H := conjugateSpanBy V C
      localModule T Mc = E ∧ V ≤ Mc.pCoreIn 2 ∧
      ∃ (hn : Mc ≤ normalizer (H : Set G)) (he : IsElementaryAbelian 2 H),
        letI := he
        V < H ∧ H ≤ M.pCoreIn 2 ⊓ Mc.pCoreIn 2 ∧
        H ≤ centralizer (V : Set G) ∧ ⁅Mc.pCoreIn 2,H⁆ ≤ E ∧
        ¬ ⁅elementaryAbelianMaxJ (T : Subgroup G),H⁆ ≤ E ∧
        IsFFModule (imageRepresentation Mc H hn) ∧
        letI : (E.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
          (Subgroup.centralizer_le_normalizer (E : Set G))
        IsPReduced 2 ((H.subgroupOf C).map (QuotientGroup.mk' (E.subgroupOf C))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z₁ D h15
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  have heq := (h.decomposable_fifteen_partner_and_normalization
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive h15).1
  have hcore := h.decomposable_five_full_partner_module_le_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive heq
  have hspan := h.partner_core_span_ff hG T hempty hM hJ hu hne hcore.2
  dsimp only at hspan
  rw [heq] at hspan
  obtain ⟨hn,he,hVH,hcores,hHV,_hJT,hff⟩ := hspan
  let := he
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMcE : Mc ≤ normalizer (E : Set G) := by
    rw [show E = localModule T Mc from heq.symm]
    exact le_normalizer_conjugateSpanBy _ _
  have hCMc : C ≤ Mc := by
    change centralizer (E : Set G) ≤ Mc
    rw [show E = localModule T Mc from heq.symm]
    exact localModule_centralizer_le_partner T Mc hu
  have hCQ : C ≤ normalizer (Mc.pCoreIn 2 : Set G) := hCMc.trans
    (Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le inf_le_left)
  have hmove : ⁅Mc.pCoreIn 2,H⁆ ≤ E := by
    rw [commutator_comm,commutator_conjugateSpanBy_of_normalized_right V C
      (Mc.pCoreIn 2) hVC hCQ]
    exact conjugateSpanBy_le ((commutator_comm V (Mc.pCoreIn 2)).trans_le hcore.1)
      (Subgroup.centralizer_le_normalizer _)
  have hout : ¬ Mc ≤ M := fun hh => hne (hMcC.1.eq_of_le hM.1.1.1 hh).symm
  have hJT := h.section_thompson_movement hG T hM hJ hTMc hout hn hMcE
    (show E ≤ V from inf_le_left) (le_conjugateSpanBy V C)
  refine ⟨heq,hcore.2,hn,he,hVH,hcores,hHV,hmove,hJT,hff,?_⟩
  exact h.decomposable_five_full_partner_span_quotient_reduced
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive heq

end CFSG.Quasithin.Chapter15.Section01
