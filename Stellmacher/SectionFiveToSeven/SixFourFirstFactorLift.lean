module
public import Stellmacher.SectionFiveToSeven.SixFourFixingFactor
public import Stellmacher.SectionTwo.FixingFactorLocalLift

/-!
# The first selected local factor in Stellmacher (6.4)

For the canonical barred action under Hypothesis Two, keep a specified raw
one-seven factor fixing a nonzero vector outside the central involutions.
There is an ambient local subgroup over the Sylow centralizer of that
vector, lying in the product of that centralizer and the full offender
preimage. Its quotient image contains the specified factor, and it
centralizes the vector.

The canonical Sylow image and (5.3) supply the native Section Two
hypotheses. The native fixing-factor lift constructs the subgroup without
assuming that the Sylow stabilizes the selected factor. Injective
local-family transport preserves its two-core, Sylow, and unique maximal
overgroup data. Mapping the native centralizer and quotient image then
gives the literal ambient conclusion.

Source: Stellmacher (6.4), Journal of Algebra 190 (1997), p.32; the barred
notation follows the journal scan and SixFourBarredAction. The later
containment of the selected four-element module in the omega/residual
commutator is a separate result.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_first_factor_lift
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥) (w : sectionSixLocalV h)
    (hwJ : ((w : P1) : H) ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H))
    (hwZ : ((w : P1) : H) ∉ omegaOneCenter S) :
    letI := sectionSixQuotientAction h
    ∀ D : Subgroup (SectionSixBarP1 h),
      SectionOne.IsOneSevenFactor (V := sectionSixLocalV h) D →
      w ∈ FixedPoints.subgroup D (sectionSixLocalV h) →
      let q := sectionSixQuotientMap h
      let E := ((SectionOne.oneE (V := sectionSixLocalV h)
        ((sectionSixSylow h : Subgroup P1).map q)).comap q).map P1.subtype
      let T := S ⊓ Subgroup.centralizer ({((w : P1) : H)} : Set H)
      ∃ F : Subgroup H, F ∈ PFamily (E ⊔ T) T ∧ F ≤ P1 ∧
        D ≤ (F.subgroupOf P1).map q ∧
        F ≤ Subgroup.centralizer ({((w : P1) : H)} : Set H) := by
  classical
  let SP := sectionSixSylow h
  let V := sectionSixLocalV h
  let q := sectionSixQuotientMap h
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = SectionTwo.cSubgroup SP := QuotientGroup.ker_mk' _
  let _ := sectionSixQuotientAction h
  intro D hD hwD
  have hsetup := sectionSix_barred_action_setup h
  have hSP : (SP : Subgroup P1).map P1.subtype = S := hsetup.sylow_image
  obtain ⟨hsol, hchar, _⟩ := lemma_five_three S0 S P1 P2 h
  have hSPne : (SP : Subgroup P1) ≠ ⊥ := by
    intro ht
    apply h.fiveOne.S_nontrivial
    rw [← hSP, ht, Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card SP := SP.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hSPne (Subgroup.card_eq_one.mp hc))
  have hsec : SectionTwo.Hypotheses P1 :=
    ⟨hsol, even_iff_two_dvd.mpr (hdvd.trans (SP : Subgroup P1).card_subgroup_dvd_card), hchar⟩
  have hwne : w ≠ 1 := by
    intro hw
    apply hwZ
    rw [hw]
    exact (omegaOneCenter S).one_mem
  have hwfix : w ∈ FixedPoints.subgroup (sectionSixBarredCritical h) V :=
    (hsetup.mem_fixedPoints_iff w).mpr hwJ
  obtain ⟨F, hF, hDF, hFw⟩ :=
    SectionTwo.fixing_factor_local_lift hsec SP q hq hker hJ w hwne hwfix D hD hwD
  let En := (SectionOne.oneE (V := V) ((SP : Subgroup P1).map q)).comap q
  let Tn := (SP : Subgroup P1) ⊓ Subgroup.centralizer ({(w : P1)} : Set P1)
  let T := S ⊓ Subgroup.centralizer ({((w : P1) : H)} : Set H)
  have hTm : Tn.map P1.subtype = T := by
    apply le_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨hSP.le (Subgroup.mem_map_of_mem P1.subtype ht.1), ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg P1.subtype (Subgroup.mem_centralizer_singleton_iff.mp ht.2)
    · rintro _ ⟨hs, hc⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp (hSP.ge hs)
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact P1.subtype_injective (Subgroup.mem_centralizer_singleton_iff.mp hc)
  obtain ⟨TF, hTF⟩ := hF.1.2.1
  let f := P1.subtype.comp F.subtype
  have hTf : (TF : Subgroup F).map f = T := by
    rw [show f = P1.subtype.comp F.subtype from rfl, ← Subgroup.map_map, hTF, hTm]
  have hcore : pCore 2 F ≠ ⊥ := by
    intro hh
    apply hF.1.2.2.1
    change (pCore 2 F).map F.subtype = ⊥
    rw [hh, Subgroup.map_bot]
  have hnot : (TF : Subgroup F) ≠ pCore 2 F := by
    intro hh
    apply hF.1.2.2.2
    rw [← hTF, hh]
    rfl
  have huniq := native_uniqueMaximalContaining F (TF : Subgroup F)
    (by rw [hTF]; exact hF.2)
  have hfamily := pFamily_range_of_injective f
    (P1.subtype_injective.comp F.subtype_injective) TF T hTf hcore hnot huniq
  have hfrange : f.range = F.map P1.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hsmall : f.range ≤ En.map P1.subtype ⊔ T := by
    rw [hfrange, ← hTm, ← Subgroup.map_sup]
    exact Subgroup.map_mono hF.1.1
  have hfamily' : f.range ∈ PFamily (En.map P1.subtype ⊔ T) T := by
    rw [pFamily_iff_pSet] at hfamily ⊢
    exact ⟨⟨hsmall, hfamily.1.2⟩, hfamily.2⟩
  refine ⟨f.range, hfamily', ?_, ?_, ?_⟩
  · rw [hfrange]
    exact Subgroup.map_subtype_le _
  · rw [hfrange, subgroupOf_map_subtype_eq]
    exact hDF
  · rw [hfrange]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg P1.subtype (Subgroup.mem_centralizer_singleton_iff.mp (hFw hx))

end Stellmacher.SectionsFiveToSeven

