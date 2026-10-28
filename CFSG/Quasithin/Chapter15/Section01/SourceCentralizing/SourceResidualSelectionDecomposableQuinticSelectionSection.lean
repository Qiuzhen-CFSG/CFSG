module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreThompson
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionDisplacement
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionDisplacement
public import Theory.GroupTheory.ReducedNormal.SylowCentralQuotient
public import Theory.GroupTheory.SylowCentralizerOfNormalizer

/-!
# The actual order-four partner section is reduced

The original partner four-group is diagonal in the two Thompson planes.
Every element of its Sylow centralizer permutes these planes and fixes the
diagonal pointwise, so its displacement on E lies in the diagonal. In the
literal quotient C_G(Uc)/Uc the image of E is therefore Sylow-central.
Its normal closure is the image of the verified elementary envelope F,
and the Sylow-central normal-closure theorem makes this image two-reduced.

The internal import intentionally reuses the generic diagonal-fixer proof
from the frozen displacement file. No reduction assertion about F before
passing to the quotient is used or asserted.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.decomposable_five_partner_four_sylow_centralizer_displacement
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
      Nat.card (localModule T Mc)=4 →
      ⁅(T:Subgroup G)⊓centralizer (localModule T Mc:Set G), thompsonFixed T V⁆≤localModule T Mc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Uc := localModule T Mc
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,_,hjoin₁,hjoin₂,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hUE : Uc≤E := (show Uc≤Uc⊔Z₁ from le_sup_left).trans_eq hjoin₁
  have hTE : (T:Subgroup G)≤normalizer (E:Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  apply commutator_le.mpr
  intro g hg e he
  apply ambient_diagonal_displacement E Z₁ Z₂ Uc inf_le_right inf_le_right hUE
    (disjoint_iff.mpr s.thompson_disjoint) hjoin₁ hjoin₂ g (hTE hg.1) hg.2 ?_ e he
  by_cases hn:g∈normalizer (plane V (c.ambientFactor d s.first).space:Set G)
  · have hh := s.thompson_normalized ⟨hg.1,hn⟩
    exact Or.inl ⟨mem_normalizer_iff_map_conj_eq.mp hh.1,mem_normalizer_iff_map_conj_eq.mp hh.2⟩
  · exact Or.inr (s.thompson_exchanges g hg.1 hn)

theorem PreparedChosenModule.decomposable_five_partner_four_fixed_span_quotient_reduced
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
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let C := centralizer (Uc:Set G)
      let F := conjugateSpanBy (thompsonFixed T V) C
      letI : (Uc.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
        (Subgroup.centralizer_le_normalizer (Uc:Set G))
      IsPReduced 2 ((F.subgroupOf C).map (QuotientGroup.mk' (Uc.subgroupOf C))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc:Set G)
  let F := conjugateSpanBy E C
  let : (Uc.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (Uc:Set G))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hUE : Uc≤E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hEC : E≤C := E.le_centralizer.trans (centralizer_le hUE)
  have hUC : Uc≤C := hUE.trans hEC
  obtain ⟨_,_,_,heF,_,_⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := heF
  have hFC : F≤C := conjugateSpanBy_le_self hEC
  let : IsElementaryAbelian 2 (F.subgroupOf C) := IsElementaryAbelian.subgroupOf hFC
  have hclosure : normalClosure (E.subgroupOf C : Set C)=F.subgroupOf C :=
    normalClosure_subgroupOf_eq_conjugateSpanBy E C hEC
  let : IsElementaryAbelian 2 (normalClosure (E.subgroupOf C : Set C)) :=
    hclosure.symm ▸ inferInstance
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTU : (T:Subgroup G)≤normalizer (Uc:Set G) :=
    hTMc.trans (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes Uc hTU
  have hmove := h.decomposable_five_partner_four_sylow_centralizer_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hdisp : ⁅E.subgroupOf C,(P:Subgroup C)⁆≤Uc.subgroupOf C := by
    apply map_le_map_iff_of_injective C.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hEC,hP,
      map_subgroupOf_eq_of_le hUC,commutator_comm]
    exact hmove
  have hr := isPReduced_normalClosure_quotient_of_sylow_displacement
    P (Uc.subgroupOf C) (E.subgroupOf C) hdisp
  rwa [hclosure] at hr

end CFSG.Quasithin.Chapter15.Section01
