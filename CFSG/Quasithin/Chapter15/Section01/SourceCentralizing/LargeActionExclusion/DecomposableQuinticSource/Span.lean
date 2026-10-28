module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Core
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Movement
public import Theory.GroupTheory.ReducedNormal.SylowCentralQuotient
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The original reduced quintic section for every partner-module size

Full normalization makes the seed-centralizer residual centralize E.
Together with the Sylow supplement, this identifies the span under C_G(E)
with the original partner span under C_G(Uc). The full original module lies
in the partner core, so this same span is elementary and lies in both cores.
Its genuine FF action and Thompson movement survive. The literal image of
H in C_G(E)/E is two-reduced by the original Sylow displacement calculation.
No equality Uc=E or order-fifteen residual hypothesis is required.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The unchanged quintic source supplies its actual common-core span and a
reduced quotient still moved by the original Thompson subgroup. -/
theorem PreparedChosenModule.decomposable_five_span_section
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
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let E := thompsonFixed T V
      let C := centralizer (E : Set G)
      let H := conjugateSpanBy V C
      V ≤ Mc.pCoreIn 2 ∧ normalizer (E : Set G) = Mc ∧
      H = conjugateSpanBy V (centralizer (localModule T Mc : Set G)) ∧
      ∃ (hn : Mc ≤ normalizer (H : Set G)) (he : IsElementaryAbelian 2 H),
        letI := he
        V < H ∧ H ≤ M.pCoreIn 2 ⊓ Mc.pCoreIn 2 ∧
        H ≤ centralizer (V : Set G) ∧
        ¬ ⁅elementaryAbelianMaxJ (T : Subgroup G),H⁆ ≤ E ∧
        IsFFModule (imageRepresentation Mc H hn) ∧
        letI : (E.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
          (Subgroup.centralizer_le_normalizer (E : Set G))
        IsPReduced 2 ((H.subgroupOf C).map (QuotientGroup.mk' (E.subgroupOf C))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  let Uc := localModule T Mc
  let C₀ := centralizer (centralInvolutions T : Set G)
  have hVQ := h.decomposable_five_le_partner_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hNE := h.decomposable_five_fixed_normalizer_eq_partner
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hMcE : Mc ≤ normalizer (E : Set G) := hNE.ge
  have hUcE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hMcC : Mc ∈ maximalTwoLocalOvergroups C₀ := hu ▸ Set.mem_singleton Mc
  have hTC₀ : (T : Subgroup G) ≤ C₀ := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hTMc : (T : Subgroup G) ≤ Mc := hTC₀.trans hMcC.2
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) := hTMc.trans hMcE
  have hTH : (T : Subgroup G) ≤ normalizer (H : Set G) :=
    normalizes_conjugateSpanBy V C (T : Subgroup G) (hM.1.2.trans h.normalized)
      (hTE.trans (normalizer_le_normalizer_centralizer _))
  have hres := (h.thompsonFixed_residual_normalized_of_le_partner_core
    hG T hempty hM hJ hu hVQ).1
  have hC₀H : C₀ ≤ normalizer (H : Set G) := by
    have hgen := congrArg (map C₀.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTC₀))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC₀] at hgen
    rw [←hgen]
    exact sup_le (hres.trans (le_normalizer_conjugateSpanBy V C)) hTH
  have hspan : H = conjugateSpanBy V (centralizer (Uc : Set G)) := by
    apply le_antisymm
    · exact conjugateSpanBy_mono le_rfl (centralizer_le hUcE)
    · exact conjugateSpanBy_le (le_conjugateSpanBy V C)
        ((centralizer_le (le_conjugateSpanBy (centralInvolutions T) Mc)).trans hC₀H)
  have hdata := h.partner_core_span_ff hG T hempty hM hJ hu hne hVQ
  dsimp only at hdata
  rw [←hspan] at hdata
  obtain ⟨hn,he,hVH,hcores,hHV,_hJT,hff⟩ := hdata
  let := he
  have hout : ¬ Mc ≤ M := fun hh => hne (hMcC.1.eq_of_le hM.1.1.1 hh).symm
  have hmove := h.section_thompson_movement hG T hM hJ hTMc hout hn hMcE
    (show E ≤ V from inf_le_left) hVH.le
  refine ⟨hVQ,hNE,hspan,hn,he,hVH,hcores,hHV,hmove,hff,?_⟩
  let : (E.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (E : Set G))
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le (show E ≤ V from inf_le_left))
  have hHC : H ≤ C := conjugateSpanBy_le_self hVC
  let : IsElementaryAbelian 2 (H.subgroupOf C) := IsElementaryAbelian.subgroupOf hHC
  have hclosure : normalClosure (V.subgroupOf C : Set C) = H.subgroupOf C :=
    normalClosure_subgroupOf_eq_conjugateSpanBy V C hVC
  let : IsElementaryAbelian 2 (normalClosure (V.subgroupOf C : Set C)) :=
    hclosure.symm ▸ inferInstance
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes E hTE
  have hdispV := h.decomposable_five_fixed_centralizer_displacement
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
  have hdisp : ⁅V.subgroupOf C,(P : Subgroup C)⁆ ≤ E.subgroupOf C := by
    apply map_le_map_iff_of_injective C.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hVC,hP]
    have hEC : E ≤ C := (show E ≤ V from inf_le_left).trans hVC
    rw [map_subgroupOf_eq_of_le hEC,commutator_comm]
    exact hdispV
  have hr := isPReduced_normalClosure_quotient_of_sylow_displacement
    P (E.subgroupOf C) (V.subgroupOf C) hdisp
  rwa [hclosure] at hr

end CFSG.Quasithin.Chapter15.Section01
