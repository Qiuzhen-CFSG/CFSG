module
public import Stellmacher.SectionFiveToSeven.SixFourResidualFactorNormalizer
public import Stellmacher.SectionFiveToSeven.SixFourNativeBaumannFixed
public import Stellmacher.UniqueMaximalContainingMap

/-!
# Local rank inputs for the canonical barred action

Under Hypothesis Two and nontrivial canonical barred critical subgroup, the
actual quotient action on the Section Six module satisfies Section One. Its
Sylow image has a unique maximal overgroup, supplements the one-seven product,
and that product contains the image of the original local two-residual.
The elementary-module instance and the named quotient action are retained.

The intrinsic P₁ data come from (5.3) and the local P-family. Nontrivial oneJ
makes the quotient Sylow nontrivial, while the quotient two-core is trivial.
Thus the Sylow image is proper, and unique maximality descends by the genuine
surjective subgroup correspondence. The normal-closure form of (3.4) identifies
oneE as the quotient two-residual joined with oneJ. The original residual and
Sylow already generate P₁, proving the required supplement after mapping.

This supplies the local hypotheses for the (1.7) rank argument in Stellmacher
(9.3), Journal of Algebra 190 (1997), p.50, `refs/files/stellmacher-n-group.pdf`.
No ambient Hypothesis Two is imposed on a quotient or on the graph group.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_barred_rank_action_setup {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    [IsElementaryAbelian 2 (sectionSixLocalV h)]
    (hJ : sectionSixBarredCritical h ≠ ⊥) :
    letI := sectionSixQuotientAction h
    SectionOne.Hypotheses (SectionSixBarP1 h) (sectionSixLocalV h) ∧
      IsUniqueMaximalContaining (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h)) ⊤ ∧
      SectionOne.oneE (V := sectionSixLocalV h)
        (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h)) ⊔
          (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h)) = ⊤ ∧
      (twoResidualAmbient (⊤ : Subgroup P1)).map (sectionSixQuotientMap h) ≤
        SectionOne.oneE (V := sectionSixLocalV h)
          (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h)) := by
  classical
  let T := sectionSixSylow h
  let q := sectionSixQuotientMap h
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = SectionTwo.cSubgroup T := QuotientGroup.ker_mk' _
  let _ := sectionSixQuotientAction h
  have hsetup := sectionSix_barred_action_setup h
  have hTm : (T : Subgroup P1).map P1.subtype = S := hsetup.sylow_image
  obtain ⟨hsol, hchar, _⟩ := lemma_five_three S0 S P1 P2 h
  have hTne : (T : Subgroup P1) ≠ ⊥ := by
    intro ht
    apply h.fiveOne.S_nontrivial
    rw [← hTm, ht, Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hTne (Subgroup.card_eq_one.mp hc))
  have hsec : SectionTwo.Hypotheses P1 :=
    ⟨hsol, even_iff_two_dvd.mpr (hdvd.trans (T : Subgroup P1).card_subgroup_dvd_card), hchar⟩
  have hP := (pFamily_iff_pSet _ _ _).mp h.fiveOne.P1_mem
  have hcore : pCore 2 P1 ≠ ⊥ := by
    intro hc
    apply hP.1.2.2.1
    change (pCore 2 P1).map P1.subtype = ⊥
    rw [hc, Subgroup.map_bot]
  have hnot : (T : Subgroup P1) ≠ pCore 2 P1 := by
    intro hc
    apply hP.1.2.2.2
    rw [← hTm, hc]
    rfl
  have huniq : IsUniqueMaximalContaining (T : Subgroup P1) (⊤ : Subgroup P1) :=
    native_uniqueMaximalContaining P1 (T : Subgroup P1) (by rw [hTm]; exact hP.2)
  have hnative : (⊤ : Subgroup P1) ∈ SectionThree.PSet ⊤ (T : Subgroup P1) := by
    have hh := pFamily_range_of_injective (MonoidHom.id P1) Function.injective_id
      T (T : Subgroup P1) (Subgroup.map_id _) hcore hnot huniq
    rw [(MonoidHom.id P1).range_eq_top_of_surjective Function.surjective_id,
      pFamily_iff_pSet] at hh
    exact hh
  let V := sectionSixLocalV h
  let X := SectionSixBarP1 h
  let U := sectionSixBarSylow h
  let J := sectionSixBarredCritical h
  let E := SectionOne.oneE (V := V) (U : Subgroup X)
  have hJS : J ≤ (U : Subgroup X) := sSup_le fun _ ha => ha.1
  have hUne : (U : Subgroup X) ≠ ⊥ := fun hb => hJ (bot_unique (hb ▸ hJS))
  have hUd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hUne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable P1 := hsol
  have hOne : SectionOne.Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (hUd.trans (U : Subgroup X).card_subgroup_dvd_card),
      SectionTwo.quotientConjugationAction_faithful T q hq hker,
      SectionTwo.lemma_two_one hsec T q hq hker⟩
  have hUproper : (U : Subgroup X) ≠ ⊤ := by
    intro ht
    have hp : (⊤ : Subgroup X) ≤ pCore 2 X :=
      le_sSup ⟨inferInstance,ht ▸ U.isPGroup'⟩
    exact hUne (bot_unique (le_top.trans (hp.trans_eq hOne.twoCore_eq_bot)))
  have huniqU := uniqueMaximalContaining_map_of_ne_top q hq
    (T : Subgroup P1) huniq hUproper
  have hthree : SectionThree.Hypotheses P1 (T : Subgroup P1) :=
    ⟨hsec.even_order,hTne,T.isPGroup'⟩
  have hEeq := SectionThree.offender_normalClosure_eq_residual_sup T hthree hnative
    hsol q hq hOne hJ
  have hRmap : (twoResidualAmbient (⊤ : Subgroup P1)).map q =
      twoResidualAmbient (⊤ : Subgroup X) :=
    map_twoResidualAmbient_of_subgroup_image ⊤ q ⊤ (Subgroup.map_top_of_surjective q hq)
  have hRE : (twoResidualAmbient (⊤ : Subgroup P1)).map q ≤ E := by
    rw [hRmap]
    change _ ≤ SectionOne.oneE (V := V) ((T : Subgroup P1).map q)
    rw [hEeq]
    exact le_sup_left
  have hRsup : twoResidualAmbient (⊤ : Subgroup P1) ⊔ (T : Subgroup P1) = ⊤ := by
    apply Subgroup.map_injective P1.subtype_injective
    rw [Subgroup.map_sup, hTm]
    have hm : (twoResidualAmbient (⊤ : Subgroup P1)).map P1.subtype =
        twoResidualAmbient P1 := map_twoResidualAmbient_of_subgroup_image
      ⊤ P1.subtype P1 (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
    rw [hm,SectionThree.twoResidual_sup_sylowImage h.fiveOne.P1_mem.1.2.1.2,
      ← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hEsup : E ⊔ (U : Subgroup X) = ⊤ := by
    apply top_unique
    rw [← Subgroup.map_top_of_surjective q hq,← hRsup,Subgroup.map_sup]
    exact sup_le_sup_right hRE _
  exact ⟨hOne,huniqU,hEsup,hRE⟩

end Stellmacher.SectionsFiveToSeven
