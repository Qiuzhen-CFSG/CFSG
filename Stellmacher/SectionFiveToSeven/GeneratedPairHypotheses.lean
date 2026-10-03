module

public import Stellmacher.SectionFiveToSeven.Result5_3

/-!
# Section Seven hypotheses for the generated pair

For a finite ambient group satisfying Hypothesis Two, its local pair satisfies
the genuine Section Seven assumptions inside the subgroup it generates. No
Hypothesis Two on that subgroup, nor a Sylow assumption on the restricted edge
group in that subgroup, is needed. This supplies the standing hypotheses for
the generated-pair coset graph while retaining the original ambient context.

The canonical `subgroupOfEquivOfLe` isomorphisms transport the actual Sylow
witnesses and two-cores, preserving nontriviality and the inequality between the
edge group and each core. Their subgroup order isomorphisms transport the
unique maximal subgroups containing the edge group. Stellmacher (5.3) supplies
solvability and characteristic two; the latter follows across the same group
isomorphisms by transporting the core-centralizer containment. Finally, the
restricted pair generates its ambient group, whose core vanishes by (5.1)'s
join-core clause and injectivity of the subtype map, not ambient core-freeness.

Source: `refs/latex/stellmacher-n-group.tex`, Hypothesis 2, (5.3), and the
standing assumptions at the start of Section 7.
-/

universe u

namespace Stellmacher.SectionsFiveToSeven.HypothesisTwo

private theorem restricted_core_map
    {H : Type u} [Group H] (P J : Subgroup H) (hPJ : P ≤ J) :
    (twoCoreIn (P.subgroupOf J)).map J.subtype = twoCoreIn P := by
  let equiv := Subgroup.subgroupOfEquivOfLe hPJ
  have hcore := congrArg (fun core : Subgroup P => core.map P.subtype)
    (pCore_map_iso 2 equiv)
  have hcomp : P.subtype.comp equiv.toMonoidHom =
      J.subtype.comp (P.subgroupOf J).subtype := by
    ext element
    rfl
  simpa only [twoCoreIn, Subgroup.map_map, hcomp] using hcore

private theorem restricted_unique_maximal
    {H : Type u} [Group H] (S P J : Subgroup H) (hPJ : P ≤ J)
    (hunique : HasUniqueMaximalOver S P) :
    HasUniqueMaximalOver (S.subgroupOf J) (P.subgroupOf J) := by
  obtain ⟨hSP, maximal, hmaximal, hSmaximal, hunique⟩ := hunique
  let equiv := Subgroup.subgroupOfEquivOfLe hPJ
  let orderIso := equiv.comapSubgroup
  have hS : orderIso (S.subgroupOf P) =
      (S.subgroupOf J).subgroupOf (P.subgroupOf J) := rfl
  refine ⟨Subgroup.comap_mono hSP, orderIso maximal,
    (orderIso.isCoatom_iff maximal).mpr hmaximal, ?_, ?_⟩
  · rw [← hS]
    exact orderIso.monotone hSmaximal
  · intro other hother hSother
    have hothermaximal : IsCoatom (orderIso.symm other) :=
      (orderIso.symm.isCoatom_iff other).mpr hother
    have hle : S.subgroupOf P ≤ orderIso.symm other := by
      apply orderIso.le_symm_apply.mpr
      simpa only [hS] using hSother
    have heq := congrArg orderIso (hunique _ hothermaximal hle)
    simpa only [OrderIso.apply_symm_apply] using heq

private theorem restricted_family
    {H : Type u} [Group H] [Finite H] (S P J : Subgroup H) (hPJ : P ≤ J)
    (hmember : P ∈ PFamily ⊤ S) :
    P.subgroupOf J ∈ PFamily ⊤ (S.subgroupOf J) := by
  obtain ⟨⟨_, ⟨hSP, sylow, hsylow⟩, hcore, hne⟩, hunique⟩ := hmember
  have hSJ := hSP.trans hPJ
  let equiv := Subgroup.subgroupOfEquivOfLe hPJ
  have hSmap := Subgroup.map_subgroupOf_eq_of_le hSJ
  have hcoremap := restricted_core_map P J hPJ
  refine ⟨⟨le_top, ⟨Subgroup.comap_mono hSP, ?_⟩, ?_, ?_⟩,
    restricted_unique_maximal S P J hPJ hunique⟩
  · have hsurjective : Function.Surjective equiv.symm.toMonoidHom := equiv.symm.surjective
    refine ⟨sylow.mapSurjective hsurjective, ?_⟩
    apply Subgroup.map_injective J.subtype_injective
    rw [hSmap, Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    have hcomp : (J.subtype.comp (P.subgroupOf J).subtype).comp
        equiv.symm.toMonoidHom = P.subtype := by
      ext element
      rfl
    rw [hcomp]
    exact hsylow
  · intro hbot
    apply hcore
    rw [← hcoremap, hbot, Subgroup.map_bot]
  · intro heq
    apply hne
    rw [← hSmap, heq, hcoremap]

private theorem restricted_characteristicTwo
    {H : Type u} [Group H] (P J : Subgroup H) (hPJ : P ≤ J)
    (hchar : IsCharacteristicTwoType P) :
    IsCharacteristicTwoType (P.subgroupOf J) := by
  let equiv := Subgroup.subgroupOfEquivOfLe hPJ
  have hcore := pCore_map_iso 2 equiv
  intro element helement
  have hcentral : equiv element ∈ Subgroup.centralizer (pCore 2 P : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    rw [← hcore] at hother
    obtain ⟨preimage, hpreimage, rfl⟩ := hother
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg equiv
      (Subgroup.mem_centralizer_iff.mp helement preimage hpreimage)
  have hmem := hchar hcentral
  rw [← hcore] at hmem
  exact (Subgroup.mem_map_iff_mem equiv.injective).mp hmem

/-- The local pair of Hypothesis Two satisfies Section Seven's standing
assumptions in its generated subgroup, without transferring Hypothesis Two. -/
public theorem generatedSectionSevenHypotheses
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    SectionSevenHypotheses (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2))
      (P2.subgroupOf (P1 ⊔ P2)) := by
  obtain ⟨hP1solvable, hP1char, hP2solvable, hP2char⟩ :=
    lemma_five_three S0 S P1 P2 h
  have hSJ : S ≤ P1 ⊔ P2 := h.fiveOne.P1_mem.1.2.1.1.trans le_sup_left
  refine
    { S_nontrivial := ?_
      P1_mem := restricted_family S P1 _ le_sup_left h.fiveOne.P1_mem
      P2_mem := restricted_family S P2 _ le_sup_right h.fiveOne.P2_mem
      generated := ?_
      P1_solvable := ?_
      P2_solvable := ?_
      P1_characteristicTwo := restricted_characteristicTwo P1 _ le_sup_left hP1char
      P2_characteristicTwo := restricted_characteristicTwo P2 _ le_sup_right hP2char
      twoCore_eq_bot := ?_ }
  · intro hbot
    apply h.fiveOne.S_nontrivial
    rw [← Subgroup.map_subgroupOf_eq_of_le hSJ, hbot, Subgroup.map_bot]
  · rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  · let := hP1solvable
    let equiv := Subgroup.subgroupOfEquivOfLe (show P1 ≤ P1 ⊔ P2 from le_sup_left)
    exact Group.isSolvable_of_isSolvable_injective
      (f := equiv.toMonoidHom) equiv.injective
  · let := hP2solvable
    let equiv := Subgroup.subgroupOfEquivOfLe (show P2 ≤ P1 ⊔ P2 from le_sup_right)
    exact Group.isSolvable_of_isSolvable_injective
      (f := equiv.toMonoidHom) equiv.injective
  · exact (Subgroup.map_eq_bot_iff_of_injective _ (P1 ⊔ P2).subtype_injective).mp
      h.fiveOne.join_twoCore_eq_bot
end Stellmacher.SectionsFiveToSeven.HypothesisTwo
