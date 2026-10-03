module
public import Stellmacher.SectionEight.EightFourFixedClosureElementary
public import Stellmacher.SectionEight.LocalQuotientSylowActionSetup
public import Stellmacher.SectionOne.LemmaOneSeven
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# A central Sylow fixed space forces the four-element center

For the original noncommuting Section Eight context with central first-step
center, suppose the actual Sylow subgroup centralizes the J-fixed space of
an exact faithful quotient witness on the initial center. Then that initial
center has order four. This is the rank-one deduction from (8.1) in the
opening of Stellmacher (8.5), Journal of Algebra 190 (1997), p.40 of
`refs/files/stellmacher-n-group.pdf`.

The image Sylow fixes the J-fixed space, so the Baumann equality (1.7)
identifies it with J. The local two-residual supplement makes the normal
closure of J the entire action group. Unique maximality descends through
the supplied surjection. In the resulting direct product of SL2(2) factors,
a factor outside the unique maximal over the Sylow supplements that Sylow.
The quotient by this normal factor is a two-group; disjointness would embed
any other order-six factor into that quotient, which is impossible. Thus
one factor is the entire action group. Its module decomposition consists
of its four-element support and the fixed space. The proved initial
residual-centralizer theorem kills that fixed space. All action-dependent
constructions retain the witness's exact action instance.
-/

open Stellmacher
namespace Stellmacher.SectionOne
universe u

private theorem sl2_product_rank_one_of_unique_maximal {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct (⊤ : Subgroup G) F)
    (hSL : ∀ D ∈ F, IsSL2Two D)
    (huniq : ∃! M : Subgroup G, IsCoatom M ∧ (S : Subgroup G) ≤ M) :
    ∃ D ∈ F, D = ⊤ := by
  classical
  obtain ⟨M, ⟨hM, hSM⟩, huniq⟩ := huniq
  have hproper (L : Subgroup G) (hSL : (S : Subgroup G) ≤ L) (hL : L ≠ ⊤) : L ≤ M := by
    obtain ⟨M', hM', hLM'⟩ := (eq_top_or_exists_le_coatom L).resolve_left hL
    rwa [huniq M' ⟨hM', hSL.trans hLM'⟩] at hLM'
  obtain ⟨D, hD, hDM⟩ : ∃ D ∈ F, ¬ D ≤ M := by
    by_contra! hall
    apply hM.1
    apply le_antisymm le_top
    rw [hprod.1]
    exact iSup_le fun D => hall D D.property
  have hDS : (S : Subgroup G) ⊔ D = ⊤ := by
    by_contra hne
    exact hDM (le_sup_right.trans (hproper _ le_sup_left hne))
  have hDnormal : D.Normal := by
    have hn := (hprod.2.1 D hD).map (⊤ : Subgroup G).subtype
      (fun g => ⟨⟨g, trivial⟩, rfl⟩)
    simpa only [Subgroup.map_subgroupOf_eq_of_le le_top] using hn
  let _ := hDnormal
  have hquot := Subgroup.quotient_isPGroup_of_sup_eq_top (S : Subgroup G) D S.isPGroup' hDS
  have hall (K : Subgroup G) (hK : K ∈ F) : K = D := by
    by_contra hne
    have hdis := hprod.2.2.1 K hK D hD hne
    let q : K →* G ⧸ D := (QuotientGroup.mk' D).comp K.subtype
    have hq : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff (f := q)).mp
      apply eq_bot_iff.mpr
      intro k hk
      apply Subtype.ext
      exact hdis.le_bot ⟨k.property, (QuotientGroup.eq_one_iff (N := D) (x := (k : G))).mp hk⟩
    have hKp := hquot.of_injective q hq
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    rw [RankOneThreeGroupAssembly.isSL2Two_card (hSL K hK)] at hn
    have hdvd : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 6)
    have : 3 ∣ (2 : ℕ) := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
    norm_num at this
  refine ⟨D, hD, le_antisymm le_top ?_⟩
  rw [hprod.1]
  exact iSup_le fun K => (hall K K.property).le

private theorem exists_oneSevenFactor_eq_top_of_unique_maximal
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hE : oneE (V := V) (S : Subgroup G) = ⊤)
    (huniq : ∃! M : Subgroup G, IsCoatom M ∧ (S : Subgroup G) ≤ M) :
    ∃ D : Subgroup G, IsOneSevenFactor (V := V) D ∧ D = ⊤ := by
  have hgen : oneSevenGenerated (G := G) (V := V) = ⊤ :=
    (oneSeven_global_identification h S).2.symm.trans hE
  have hprod := (oneSeven_global_product h S).2.1
  rw [hgen] at hprod
  obtain ⟨D, hD, htop⟩ := sl2_product_rank_one_of_unique_maximal S
    (oneSevenFactors (G := G) (V := V)) hprod
    (fun D hD => ((mem_oneSevenFactors_iff D).mp hD).1) huniq
  exact ⟨D, (mem_oneSevenFactors_iff D).mp hD, htop⟩

end Stellmacher.SectionOne

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem unique_coatom_image
    {G K : Type u} [Group G] [Group K] [Finite K]
    (f : G →* K) (hsurj : Function.Surjective f) (T : Subgroup G)
    (huniq : ∃! M : Subgroup G, IsCoatom M ∧ T ≤ M)
    (hproper : T.map f ≠ ⊤) :
    ∃! M : Subgroup K, IsCoatom M ∧ T.map f ≤ M := by
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom (T.map f)).resolve_left hproper
  obtain ⟨N, _, hN⟩ := huniq
  refine ⟨M, ⟨hM, hTM⟩, ?_⟩
  intro L hL
  apply Subgroup.comap_injective hsurj
  exact (hN (L.comap f) ⟨Subgroup.isCoatom_comap_of_surjective hsurj hL.1,
    Subgroup.map_le_iff_le_comap.mp hL.2⟩).trans
      (hN (M.comap f) ⟨Subgroup.isCoatom_comap_of_surjective hsurj hM,
        Subgroup.map_le_iff_le_comap.mp hTM⟩).symm

/-- Centralizing the actual J-fixed space forces a single four-element support. -/
public theorem eight_five_center_card_four_of_sylow_centralizes_fixed
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hfix : S ≤ Subgroup.centralizer (w.oneJFixedPoints S : Set H)) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  classical
  have htriv := eight_four_initial_residual_center_trivial ctx hcenter
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hlocal := (local_quotient_sylow_action_setup h Γ cp w).1
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨hSP, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := Za) Sb
  let E := SectionOne.oneE (V := Za) Sb
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hB : SectionOne.oneB (V := Za) Sb = Sb := by
    apply inf_eq_left.mpr
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    obtain ⟨s, hs, rfl⟩ := hb
    apply Subtype.ext
    change ((w.action (w.projection s)) v : H) = v
    rw [w.action_compatible]
    have hF : (v : H) ∈ w.oneJFixedPoints S :=
      Subgroup.mem_map_of_mem Za.subtype hv
    have hcomm := Subgroup.mem_centralizer_iff.mp (hfix hs) (v : H) hF
    change (v : H) * (s : H) = (s : H) * (v : H) at hcomm
    rw [← hcomm, mul_inv_cancel_right]
  have hJS : J = Sb := by
    have hh := SectionOne.oneSeven_baumann_eq_j hlocal Ub
    rw [hUb, hB] at hh
    exact hh.symm
  have hEtop : E = ⊤ := by
    have hres := lemma_eight_one_residual_join ctx w
    change E = ((EAt Γ cp.a).subgroupOf P).map w.projection ⊔ J at hres
    rw [hres, hJS, ← Subgroup.map_sup]
    have hRS : (EAt Γ cp.a).subgroupOf P ⊔ S.subgroupOf P = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      have hEaP : EAt Γ cp.a ≤ P := by
        rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
        exact Subgroup.map_subtype_le _
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEaP,
        Subgroup.map_subgroupOf_eq_of_le hSP, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
      exact SectionThree.twoResidual_sup_sylowImage ⟨U, hU⟩
    rw [hRS, Subgroup.map_top_of_surjective _ w.surjective]
  have hUne : (Ub : Subgroup w.X) ≠ ⊤ := by
    intro htop
    have hp : IsPGroup 2 w.X := by
      have hp := Ub.isPGroup'
      rw [htop] at hp
      exact hp.of_surjective (⊤ : Subgroup w.X).subtype (fun x => ⟨⟨x, trivial⟩, rfl⟩)
    have hcore : pCore 2 w.X = ⊤ := by
      apply top_unique
      exact le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    have hbad : (⊤ : Subgroup w.X) = ⊥ := hcore.symm.trans hlocal.twoCore_eq_bot
    have hcard : Nat.card w.X = 1 := by
      simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using Subgroup.card_eq_one.mpr hbad
    have heven := hlocal.G_even
    rw [hcard] at heven
    norm_num at heven
  have huniqP : ∃! M : Subgroup P, IsCoatom M ∧ (U : Subgroup P) ≤ M := by
    obtain ⟨_, M, hM, hSM, huniq⟩ := hP.1.2
    refine ⟨M, ⟨hM, ?_⟩, ?_⟩
    · rw [hUS]
      exact hSM
    · intro N hN
      exact huniq N hN.1 (by rw [← hUS]; exact hN.2)
  have huniq := unique_coatom_image w.projection w.surjective (U : Subgroup P) huniqP hUne
  have hEtop' : SectionOne.oneE (V := Za) (Ub : Subgroup w.X) = ⊤ := by
    rw [hUb]
    exact hEtop
  obtain ⟨D, hD, hDtop⟩ :=
    SectionOne.exists_oneSevenFactor_eq_top_of_unique_maximal hlocal Ub hEtop' huniq
  have hEzero : FixedPoints.subgroup (⊤ : Subgroup w.X) Za = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hvres : v ∈ FixedPoints.subgroup
        (((EAt Γ cp.a).subgroupOf P).map w.projection) Za :=
      fun r => hv ⟨r, trivial⟩
    have hEaP : EAt Γ cp.a ≤ P := by
      rw [show EAt Γ cp.a = twoResidualIn P from Γ.twoResidualAt_def cp.a]
      exact Subgroup.map_subtype_le _
    have hvmap := Subgroup.mem_map_of_mem Za.subtype hvres
    rw [w.fixedPoints_map_subtype (EAt Γ cp.a) hEaP, htriv] at hvmap
    exact Subtype.ext hvmap
  have hmodule := SectionOne.oneSevenFactor_module_product hlocal
    (fun _ : Fin 1 => D) (fun _ => hD) (fun _ _ _ => Subsingleton.elim _ _)
    (⊤ : Subgroup w.X) (by simp [hDtop])
  have hgen := hmodule.1
  simp only [iSup_option, iSup_unique] at hgen
  change (⊤ : Subgroup Za) = FixedPoints.subgroup (⊤ : Subgroup w.X) Za ⊔ commutatorAction D Za at hgen
  rw [hEzero, bot_sup_eq] at hgen
  have hcard := hD.2.2.1
  rw [← hgen] at hcard
  simpa using hcard

end Stellmacher.SectionEight
