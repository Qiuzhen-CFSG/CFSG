module
public import Stellmacher.SectionNine.NineThreeRankData
public import Stellmacher.SectionNine.NineThreeCanonicalFixedIndex
public import Stellmacher.SectionFiveToSeven.SixFourRankActionSetup
public import Stellmacher.SectionFiveToSeven.SixFourCanonicalActionFixedIndex
public import Stellmacher.SectionOne.SmallFixedIndexRank

/-!
# Canonical rank-two data without a native Thompson-action assumption

For the actual normalized extraction pair with initial center larger than
four, nontriviality of the canonical barred critical subgroup gives the full
rank-two record: center order sixteen, two one-seven factors, and the exact
local action hypotheses for wreath recognition.

The initial center maps injectively to the intrinsic Section Six module.
The true local P-set gives the canonical quotient hypotheses, unique maximality
and residual supplement. The (7.5) residual centralizer makes the oneE-fixed
complement trivial. Apply (6.4) directly to vectors fixed by the full canonical
critical preimage: the geometric center overlap and its exact index four bound
the canonical fixed space. Cardinal transport gives the hypothesis of the
one-seven rank theorem. The proof never identifies native and global offenders.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), pp.49–50,
`refs/files/stellmacher-n-group.pdf`. The explicit barred nontriviality can be
supplied either by native nontrivial action or by an actual quadratic offender
in the contrary branch. Existing native wrappers retain their public APIs.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A K : Subgroup G) :
    (A ⊓ Subgroup.centralizer (K : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer (K.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f ha.1, ?_⟩
    change f a ∈ Subgroup.centralizer (K.map f : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp ha.2 k hk)
  · rintro _ ⟨⟨a, ha, rfl⟩, hcent⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    change a ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply hf
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp hcent (f k) (Subgroup.mem_map_of_mem f hk)


public theorem nine_three_canonical_action_rank_data
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJ : sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥) :
    NineThreeNativeActionRankData ctx := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.hypothesisTwo
  let V := sectionSixLocalV h
  let U := sectionSixBarSylow h
  let q := sectionSixQuotientMap h
  let _ := sectionSixQuotientAction h
  have hsetup := sectionSix_barred_action_setup h
  have hamb := nine_two_ambient_setup ctx
  have hGa : (GAt Γ cp.a).map embedding = P1 := hamb.2.1
  have hZa : (ZAt Γ cp.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx hGa
  have hVP : V.map P1.subtype = sectionSixV S P1 := hsetup.localV_image
  have hcardV : Nat.card V = Nat.card (ZAt Γ cp.a) := by
    rw [← Subgroup.card_map_of_injective P1.subtype_injective,hVP,← hZa,
      Subgroup.card_map_of_injective ctx.embedding_injective]
  obtain ⟨hsol,hchar,_⟩ := lemma_five_three S0 S P1 P2 h
  have hSPne : (sectionSixSylow h : Subgroup P1) ≠ ⊥ := by
    intro he
    apply h.fiveOne.S_nontrivial
    rw [← hsetup.sylow_image,he,Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card (sectionSixSylow h) :=
    (sectionSixSylow h).isPGroup'.card_eq_or_dvd.resolve_left
      (fun he => hSPne (Subgroup.card_eq_one.mp he))
  have hsec : SectionTwo.Hypotheses P1 := ⟨hsol,
    even_iff_two_dvd.mpr (hdvd.trans (sectionSixSylow h : Subgroup P1).card_subgroup_dvd_card),hchar⟩
  let _ : IsElementaryAbelian 2 V :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec (sectionSixSylow h)).2
  obtain ⟨hOne,huniq,hgen,hRE⟩ := sixFour_barred_rank_action_setup h hJ
  let E := SectionOne.oneE (V := V) (U : Subgroup (SectionSixBarP1 h))
  have hResP : (EAt Γ cp.a).map embedding = twoResidualAmbient P1 := by
    change (e Γ cp.a).map embedding = _
    rw [CosetGraphContext.e,Γ.twoResidualAt_def]
    change (twoResidualAmbient (GAt Γ cp.a)).map embedding = _
    exact map_twoResidualAmbient_of_subgroup_image _ embedding P1 hGa
  have hRn : (twoResidualAmbient (⊤ : Subgroup P1)).map P1.subtype =
      twoResidualAmbient P1 := map_twoResidualAmbient_of_subgroup_image
    ⊤ P1.subtype P1 (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
  have hZcore : ZAt Γ cp.a ≤ QAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hlocalfix : ZAt Γ cp.a ⊓ Subgroup.centralizer (EAt Γ cp.a : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hZcore).trans_eq
      (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).centralizer_residual)
  have hambfix : sectionSixV S P1 ⊓ Subgroup.centralizer
      (twoResidualAmbient P1 : Set H) = ⊥ := by
    rw [← hZa,← hResP,← map_inf_centralizer embedding ctx.embedding_injective,
      hlocalfix,Subgroup.map_bot]
  have hfixE : FixedPoints.subgroup E V = ⊥ := by
    apply bot_unique
    intro v hv
    have hfix : ((v : P1) : H) ∈ sectionSixV S P1 ⊓
        Subgroup.centralizer (twoResidualAmbient P1 : Set H) := by
      refine ⟨hVP ▸ Subgroup.mem_map_of_mem P1.subtype v.property,?_⟩
      change ((v : P1) : H) ∈ Subgroup.centralizer (twoResidualAmbient P1 : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      rw [← hRn] at hr
      obtain ⟨r0,hr0,rfl⟩ := hr
      have he := (FixedPoints.mem_subgroup (M := E) (a := v)).mp hv
        ⟨q r0,hRE (Subgroup.mem_map_of_mem q hr0)⟩
      have he' := congrArg (fun v : V => ((v : P1) : H)) he
      change ((q r0 • v : V) : H) = ((v : P1) : H) at he'
      rw [SectionTwo.quotientConjugationAction_smul_coe (sectionSixSylow h)
        q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)] at he'
      change (r0 : H) * ((v : P1) : H) * (r0 : H)⁻¹ = ((v : P1) : H) at he'
      exact mul_inv_eq_iff_eq_mul.mp he'
    rw [hambfix] at hfix
    exact Subtype.ext (P1.subtype_injective hfix)
  have hnext := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
  have hOm : (ZAt Γ cp.firstStep).map embedding = omegaOneCenter S := by
    rw [show ZAt Γ cp.firstStep = omegaOneCenter T from hnext.1,← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  have hKMap : ((ZAt Γ cp.a) ⊓
      (Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H)).comap embedding).map
        embedding = sectionSixV S P1 ⊓
          Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) := by
    rw [Subgroup.map_inf _ _ _ ctx.embedding_injective,hZa,
      Subgroup.map_comap_eq]
    have hr : sectionSixV S P1 ≤ embedding.range := hZa ▸ Subgroup.map_le_range embedding (ZAt Γ cp.a)
    exact le_antisymm (inf_le_inf_left _ inf_le_right)
      (le_inf inf_le_left (le_inf (inf_le_left.trans hr) inf_le_right))
  have hbound : Nat.card (sectionSixV S P1 ⊓
      Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) : Subgroup H) ≤
        4 * Nat.card (omegaOneCenter S) := by
    rw [← hKMap,← hOm,Subgroup.card_map_of_injective ctx.embedding_injective,
      Subgroup.card_map_of_injective ctx.embedding_injective]
    exact nine_three_canonical_fixed_index_graph ctx hb hlarge first second config hJ
  have hindex := sixFour_canonical_action_fixed_index_le_four h hbound
  have hlargeV : 4 < Nat.card V := hcardV ▸ hlarge
  have hc := SectionOne.oneSeven_card_sixteen_of_small_fixed_index hOne U hJ hgen huniq
    hfixE hlargeV hindex
  exact ⟨inferInstance,hcardV.symm.trans hc.1,hJ,hOne,huniq,hgen,hfixE,hc.2⟩

end Stellmacher.SectionNine
