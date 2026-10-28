module
public import Stellmacher.SectionEight.EightThreeCoreBound
public import Stellmacher.SectionEight.EightThreeThompsonNotCore
public import Stellmacher.SectionTwo.ThompsonResidualBaumann
public import Stellmacher.SectionThree.LocalCoreQuotientOddResidual

/-!
# The final action comparison in Stellmacher (8.3)

Suppose the initial core Qa equals its elementary center module Za and lies
in the next core T. Then the Baumann subgroup of the actual common Sylow
lies in T. This contradicts (6.1) in the parent theorem.

Work in the native initial stabilizer and identify its original Section Two
module with Za. Characteristic two and the elementary core identify the
module centralizer with the core. The smaller Thompson subgroup J(T) is
normal in the common Sylow and cannot lie in Qa: otherwise maximal
elementary comparison would make it Qa, normal under both edge stabilizers.
Lemma (3.4) therefore gives the full residual commutator with J(T).
The core quotient residual has odd order by (3.3). The smaller-Thompson
action comparison, using the actual quotient action and global (1.7)
factor saturation, forces Baumann into T.

Every native subgroup and quotient uses the supplied graph edge and Sylow
image; the final injective subtype map returns the literal ambient bound.
This expands the last (2.2)/(8.1) action comparison in Stellmacher (8.3),
journal p38, with the shared raw-factor results from (1.7).
Source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_three_action_comparison
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcore : QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a)
    (hcontained : QAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    baumannIn S ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Q := q Γ cp.a
  let TA := q Γ cp.firstStep
  let T := TA.subgroupOf P
  have hloc := (SevenSix.edge_local_data h Γ cp).1
  have hPset := (pFamily_iff_pSet _ _ _).mp hloc.1
  obtain ⟨hSP,U,hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  have hUne : (U : Subgroup P) ≠ ⊥ := by
    intro hb
    apply h.S_nontrivial
    rw [← hU,hb,Subgroup.map_bot]
  have heven : Even (Nat.card P) := by
    have hd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hc => hUne (Subgroup.card_eq_one.mp hc))
    exact even_iff_two_dvd.mpr (hd.trans (Subgroup.card_subgroup_dvd_card (U : Subgroup P)))
  have hsec : SectionTwo.Hypotheses P :=
    ⟨hloc.2,heven,(SevenSix.edge_characteristic_data h Γ cp).1⟩
  have h3 : SectionThree.Hypotheses P (U : Subgroup P) := ⟨heven,hUne,U.isPGroup'⟩
  have hcoreNe : pCore 2 P ≠ ⊥ := by
    intro hb
    apply hPset.1.2.2.1
    change (pCore 2 P).map P.subtype = ⊥
    rw [hb,Subgroup.map_bot]
  have hUneCore : (U : Subgroup P) ≠ pCore 2 P := by
    intro he
    apply hPset.1.2.2.2
    exact hU.symm.trans (congrArg (fun A : Subgroup P => A.map P.subtype) he)
  have huniq : IsUniqueMaximalContaining (U : Subgroup P) (⊤ : Subgroup P) :=
    native_uniqueMaximalContaining P (U : Subgroup P) (by rw [hU]; exact hPset.2)
  have hnative : (⊤ : Subgroup P) ∈ SectionThree.PSet ⊤ (U : Subgroup P) := by
    have hh := pFamily_range_of_injective (MonoidHom.id P) Function.injective_id U
      (U : Subgroup P) (Subgroup.map_id _) hcoreNe hUneCore huniq
    rw [(MonoidHom.id P).range_eq_top_of_surjective Function.surjective_id,pFamily_iff_pSet] at hh
    exact hh
  let V := SectionTwo.vSubgroup U
  have hVmap : V.map P.subtype = z Γ cp.a := vertexZ_eq_local_vSubgroup Γ cp.a U
  have hQmap : (pCore 2 P).map P.subtype = Q := (Γ.twoCoreAt_def cp.a).symm
  have hVcore : V = pCore 2 P := by
    apply Subgroup.map_injective P.subtype_injective
    exact hVmap.trans (hcore.symm.trans hQmap.symm)
  let _ : IsElementaryAbelian 2 V := (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec U).2
  let _ : IsMulCommutative (pCore 2 P) := hVcore ▸ (inferInstance : IsMulCommutative V)
  have hCV : SectionTwo.cSubgroup U = pCore 2 P := by
    change Subgroup.centralizer (V : Set P) = pCore 2 P
    rw [hVcore]
    exact le_antisymm hsec.centralizer_twoCore_le
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  let π := QuotientGroup.mk' (pCore 2 P)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = SectionTwo.cSubgroup U := by rw [QuotientGroup.ker_mk', hCV]
  have hTS : TA ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hTP : TA ≤ P := hTS.trans hSP
  have hTmap : T.map P.subtype = TA := Subgroup.map_subgroupOf_eq_of_le hTP
  have hTU : T ≤ (U : Subgroup P) := by rw [hUS]; exact Subgroup.subgroupOf_mono P hTS
  have hVT : V ≤ T := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hVmap,hTmap]
    exact hcore.symm.le.trans hcontained
  have hCT : π.ker ≤ T := by rw [hker,hCV,← hVcore]; exact hVT
  have hSPb : S ≤ Pb := (SevenSix.edge_sylow_data h Γ cp).2.1
  have hPbT : Pb ≤ Subgroup.normalizer (TA : Set H) := by
    rw [show TA = twoCoreIn Pb from Γ.twoCoreAt_def cp.firstStep]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hUnT : (U : Subgroup P) ≤ Subgroup.normalizer (T : Set P) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs t ht
    have hsS : (s : H) ∈ S := by
      exact hU.le (Subgroup.mem_map_of_mem P.subtype hs)
    exact Subgroup.le_normalizer_iff.mp hPbT (s : H) (hSPb hsS) t ht
  have hJn : ((elementaryAbelianMaxJ T).subgroupOf (U : Subgroup P)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((sSup_le fun _ ha => ha.1).trans hTU)).mpr
    intro s hs
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ T).map (MulAut.conj s).toMonoidHom = elementaryAbelianMaxJ T
    rw [← elementaryAbelianMaxJ_map_equiv]
    have ht : T.map (MulAut.conj s).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUnT hs)
    rw [ht]
  have hJmap : (elementaryAbelianMaxJ T).map P.subtype = elementaryAbelianMaxJ TA := by
    rw [← elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective,hTmap]
  have hJnot : ¬ elementaryAbelianMaxJ T ≤ pCore 2 P := by
    intro hc
    apply eight_three_thompson_not_le_core ctx hcore hcontained
    have hm := Subgroup.map_mono (f := P.subtype) hc
    rwa [hJmap,hQmap] at hm
  have hTop : twoCoreAmbient (⊤ : Subgroup P) = pCore 2 P :=
    pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P)
  have hnot : ¬ elementaryAbelianMaxJ T ≤ twoCoreAmbient (⊤ : Subgroup P) := by
    rwa [hTop]
  have hoddQ := SectionThree.odd_card_twoResidual_of_core_quotient
    (U : Subgroup P) h3 hnative hsec.solvable π hπ (QuotientGroup.ker_mk' _)
  have hodd : Odd (Nat.card ((twoResidualAmbient (⊤ : Subgroup P)).map π)) := by
    rw [map_twoResidualAmbient_of_subgroup_image ⊤ π ⊤ (Subgroup.map_top_of_surjective π hπ)]
    exact hoddQ
  let _ := SectionTwo.quotientConjugationAction U π hπ hker
  have hJTne : (elementaryAbelianMaxJ T).map π ≠ ⊥ := by
    intro hb
    apply hJnot
    simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
  let Ub := U.mapSurjective hπ
  have hUbne : (Ub : Subgroup (P ⧸ pCore 2 P)) ≠ ⊥ := by
    intro hb
    apply hJTne
    exact bot_unique ((Subgroup.map_mono ((sSup_le fun _ ha => ha.1).trans hTU)).trans_eq hb)
  have h2 : 2 ∣ Nat.card Ub := Ub.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hUbne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable P := hsec.solvable
  have hOne : SectionOne.Hypotheses (P ⧸ pCore 2 P) V :=
    ⟨Group.isSolvable_of_surjective hπ,
      even_iff_two_dvd.mpr
        (h2.trans (Subgroup.card_subgroup_dvd_card (Ub : Subgroup (P ⧸ pCore 2 P)))),
      SectionTwo.quotientConjugationAction_faithful U π hπ hker,
      SectionTwo.lemma_two_one hsec U π hπ hker⟩
  let B := (U : Subgroup P) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (U : Subgroup P)) : Set P)
  have hBT := SectionTwo.baumann_le_of_thompson_residual hsec U h3 hnative π hπ hker
    B T rfl hTU hVT hCT hJn hnot hodd hOne
  have hBmap : B.map P.subtype = baumannIn S := by
    rw [baumann_map_injective P.subtype P.subtype_injective,hU]
    rfl
  have hm := Subgroup.map_mono (f := P.subtype) hBT
  rwa [hBmap,hTmap] at hm

end Stellmacher.SectionEight
