module
public import Stellmacher.SectionFiveToSeven.SixFourFirstFactorLift
public import Stellmacher.SectionTwo.SelectedFactorOmegaResidualContainment

/-!
# The selected factor module in the ambient commutator of (6.4)

For the canonical quotient action under Hypothesis Two, assume its critical
subgroup is nontrivial. If a subgroup F of P1 has quotient image containing
a specified raw one-seven factor D, the corresponding ambient four-element
module lies in [Omega1(Z(S)), O^2(F)]. In particular this applies to the
witness of `sixFour_first_factor_lift`, which is re-exported here.

The local-family data and (5.3) supply the native Section Two hypotheses.
Apply `selected_factor_omega_residual_containment` inside P1, then map its
conclusion along the inclusion into the ambient group. Injective
omega-center transport and residual-image transport identify the literal
ambient commutator. The same named quotient action and selected D are
retained throughout; no factor invariance is assumed.

Source: Stellmacher (6.4), Journal of Algebra 190 (1997), p.32, the selected
Vj contained in U=[Omega1(Z(S)), O^2(F1)]. Barred notation follows the journal
scan accompanying refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

/-- The specified factor module lies in the literal ambient omega-residual commutator. -/
public theorem sixFour_selected_module_containment
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥) :
    letI := sectionSixQuotientAction h
    ∀ D : Subgroup (SectionSixBarP1 h),
      SectionOne.IsOneSevenFactor (V := sectionSixLocalV h) D →
      ∀ F : Subgroup H, F ≤ P1 →
        D ≤ (F.subgroupOf P1).map (sectionSixQuotientMap h) →
        (commutatorAction D (sectionSixLocalV h)).map
          (P1.subtype.comp (sectionSixLocalV h).subtype) ≤
        ⁅omegaOneCenter S, twoResidualAmbient F⁆ := by
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
  intro D hD F hFP hDF
  have hc := SectionTwo.selected_factor_omega_residual_containment
    hsec T hnative q hq hker hJ D hD (F.subgroupOf P1) hDF
  have hm := Subgroup.map_mono (f := P1.subtype) hc
  rw [Subgroup.map_map, Subgroup.map_commutator,
    ← omegaOneCenterAmbient_map_injective P1.subtype P1.subtype_injective,
    hTm, map_twoResidualAmbient_of_subgroup_image (F.subgroupOf P1)
      P1.subtype F (Subgroup.map_subgroupOf_eq_of_le hFP)] at hm
  exact hm

end Stellmacher.SectionsFiveToSeven
