module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.OrbitOmega
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Restrictions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SourceBlockSelection

/-!
# The original corank-one Omega-center escape

E.6.7 selects an actual A₃/A₅ block in H = C_G(U). The characteristic span
of all its small-block moved modules is nontrivial, lies in O₂(H) ≤ C_T(V),
and is normalized by N_T(U). Since U ≤ Z(H), the span is disjoint from U.
A nontrivial normal subgroup of the two-group N_T(U) contains a central
involution, which consequently lies outside U.

The original center-intersection alternative supplies characteristic two
through the proved E.6.6(4). No block, orbit, module or earlier-source premise
is left explicit. Source: Aschbacher–Smith, E.6.10(4), printed pp.248–249.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06
open ChapterC Blocks.OrbitOmega
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U : Subgroup G}

/-- E.6.10(4), under its original obstruction, corank and local alternatives. -/
theorem HypothesisE61.source_omega_center_not_le
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ∈ obstructionFamily M V) (hc : subgroupCorank V U = 1)
    (hfit : U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥ ∨
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G))) :
    ¬ Stellmacher.omegaOneCenterAmbient ((T : Subgroup G) ⊓ normalizer (U : Set G)) ≤ U := by
  let H := centralizer (U : Set G)
  have hf : generalizedFitting H = pCore 2 H :=
    h.lemma_E_6_10_1 (source_earlierLocalFacts h) hU hfit
  obtain ⟨L, ⟨hLH, hLB, ha⟩, _⟩ :=
    Hyperplanes.Enlargement.source_earlierBlockSelection h U hU ⟨hU.1, hc⟩ hf
  have ha' : IsAlternatingBlock (L.subgroupOf H) 3 ∨
      IsAlternatingBlock (L.subgroupOf H) 5 :=
    ha.imp (RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hLH).symm)
      (RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hLH).symm)
  let D := (smallBlockModuleSpan H).map H.subtype
  let : (smallBlockModuleSpan H).Characteristic := smallBlockModuleSpan_characteristic
  have hDH : D ≤ H := map_subtype_le _
  have hDne : D ≠ ⊥ := by
    intro he
    exact smallBlockModuleSpan_ne_bot (L.subgroupOf H) hLB ha'
      ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  have hDT : D ≤ (T : Subgroup G) := by
    have hh : D ≤ (S : Subgroup H).map H.subtype :=
      (map_mono smallBlockModuleSpan_le_core).trans (H.pCoreIn_le_sylow S)
    rw [hS] at hh
    exact hh.trans inf_le_left
  have hDS : D ≤ (T : Subgroup G) ⊓ normalizer (U : Set G) :=
    le_inf hDT (hDH.trans (Subgroup.centralizer_le_normalizer _))
  have hn : normalizer (U : Set G) ≤ normalizer (D : Set G) :=
    (normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image H (smallBlockModuleSpan H))
  have hDn : (D.subgroupOf ((T : Subgroup G) ⊓ normalizer (U : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer (inf_le_right.trans hn)
  have hDU : Disjoint D U := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro x ⟨⟨d, hd, rfl⟩, hu⟩
    have hdZ : d ∈ center H := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (c.property d hu).symm
    have hd1 : d = 1 := mem_bot.mp
      (smallBlockModuleSpan_inf_center_eq_bot hf ▸
        (show d ∈ smallBlockModuleSpan H ⊓ center H from ⟨hd, hdZ⟩))
    exact congrArg H.subtype hd1
  exact omega_center_not_le_of_normal_disjoint (T : Subgroup G) U D T.isPGroup'
    hDS hDn hDne hDU

end CFSG.Quasithin.ChapterE.Section06
