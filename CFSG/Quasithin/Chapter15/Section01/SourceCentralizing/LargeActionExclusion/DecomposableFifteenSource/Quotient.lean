module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Core
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Span
public import Theory.GroupTheory.ReducedNormal.SylowCentralQuotient
public import Theory.GroupTheory.SylowCentralizerOfNormalizer

/-!
# The actual quintic partner span modulo its fixed subgroup

When the partner module equals the original Thompson fixed subgroup E,
the whole chosen module lies in the partner core and its centralizer span
H is elementary abelian. The original Sylow centralizer of E displaces
V only into E. Consequently the image of H in C_G(E)/E is reduced.
All groups and quotient maps are the literal original subgroups.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal centralizer quotient of the original partner span is
two-reduced when the partner module is the whole Thompson fixed subgroup. -/
theorem PreparedChosenModule.decomposable_five_full_partner_span_quotient_reduced
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
      localModule T Mc = thompsonFixed T V →
      let E := thompsonFixed T V
      let C := centralizer (E : Set G)
      let H := conjugateSpanBy V C
      letI : (E.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
        (Subgroup.centralizer_le_normalizer (E : Set G))
      IsPReduced 2 ((H.subgroupOf C).map (QuotientGroup.mk' (E.subgroupOf C))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  let : (E.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (E : Set G))
  have hVQ := (h.decomposable_five_full_partner_module_le_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hUcEq).2
  obtain ⟨_hn,he,_hspan⟩ := h.partner_core_span_ff hG T hempty hM hJ hu hne hVQ
  have heH : IsElementaryAbelian 2 H := by
    change IsElementaryAbelian 2 (conjugateSpanBy V
      (centralizer (localModule T Mc : Set G))) at he
    rw [hUcEq] at he
    exact he
  let := heH
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le (show E ≤ V from inf_le_left))
  have hHC : H ≤ C := conjugateSpanBy_le_self hVC
  let : IsElementaryAbelian 2 (H.subgroupOf C) := IsElementaryAbelian.subgroupOf hHC
  have hclosure : normalClosure (V.subgroupOf C : Set C) = H.subgroupOf C :=
    normalClosure_subgroupOf_eq_conjugateSpanBy V C hVC
  let : IsElementaryAbelian 2 (normalClosure (V.subgroupOf C : Set C)) :=
    hclosure.symm ▸ inferInstance
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes E hTE
  have hmove := h.decomposable_five_fixed_centralizer_displacement
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
  have hdisp : ⁅V.subgroupOf C,(P : Subgroup C)⁆ ≤ E.subgroupOf C := by
    apply map_le_map_iff_of_injective C.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hVC,hP]
    have hEC : E ≤ C := (show E ≤ V from inf_le_left).trans hVC
    rw [map_subgroupOf_eq_of_le hEC,commutator_comm]
    exact hmove
  have hr := isPReduced_normalClosure_quotient_of_sylow_displacement
    P (E.subgroupOf C) (V.subgroupOf C) hdisp
  rwa [hclosure] at hr

end CFSG.Quasithin.Chapter15.Section01
