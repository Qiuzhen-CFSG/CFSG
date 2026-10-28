module

public import Stellmacher.SectionEight.GeneratedEightThree
public import Stellmacher.SectionEight.GeneratedEightFiveVectorCriterion
public import Stellmacher.SectionThree.NormalSubgroupCoreControl

public import Stellmacher.SectionEight.GeneratedEightFiveActionFromFour
public import Stellmacher.TwoResidualSylowSupplement
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Stellmacher.SectionEight.EightFourFixedClosureControl
public import Stellmacher.QuotientModuleCommutator
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.SectionOne.OneSevenFixedCommutator
public import Stellmacher.SectionEight.LemmaEightOneResidualJoin
public import Stellmacher.SectionEight.LemmaEightOneOffender
public import Stellmacher.SectionEight.LocalQuotientHypotheses
public import Stellmacher.SectionThree.NormalClosureResidualJoin
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionEight.EightFourFixedClosureElementary
public import Stellmacher.SectionEight.LocalQuotientSylowActionSetup
public import Stellmacher.SectionOne.LemmaOneSeven
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Generated center order four from fixed-subgroup normality

The graph-preserving local context suffices for the center-free residual
centralizer calculation, the exact action residual-join formula, and the
rank-one deduction from Sylow centralization of the fixed space. Genuine
ambient (8.3) then gives fixed-vector centralizer generation under the exact
fixed-subgroup normality premise. Hypothesis Two is never imposed on the join.

The local residual-join and residual-centralizer calculations are re-exported
from their lower owning modules `LemmaEightOneResidualJoin` and
`EightFourFixedClosureElementary`, with the same graph and faithful action.

The ambient-backed (6.4) vector criterion puts every fixed vector in the next
center. Its centrality makes the common Sylow centralize the fixed subgroup,
so the rank-one theorem gives order four for the unchanged initial center.
Source: Stellmacher (8.3) and the first paragraph of (8.5), printed pp.38–40.
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
public theorem eight_five_center_card_four_of_sylow_centralizes_fixed_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hfix : S ≤ Subgroup.centralizer (w.oneJFixedPoints S : Set H)) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  classical
  have htriv := eight_four_initial_residual_center_trivial_local ctx hcenter
  let h := ctx.sectionSeven
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
    have hres := lemma_eight_one_residual_join_local ctx w
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

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix

private theorem fixed_normal_centralizer_generates
    {G : Type*} [Group G] [Finite G]
    (S P F T : Subgroup G) (h : SectionThree.Hypotheses G S)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hFN : NormalIn F P) (hTS : T ≤ S)
    (hTF : T ≤ Subgroup.centralizer (F : Set G))
    (hTnot : ¬ T ≤ twoCoreAmbient P) :
    (P ⊓ Subgroup.centralizer (F : Set G)) ⊔ S = P := by
  let K := P ⊓ Subgroup.centralizer (F : Set G)
  have hSP : S ≤ P := by
    obtain ⟨R,hR⟩ := hP.1.2.1
    rw [← hR]
    exact Subgroup.map_subtype_le _
  have hKN : (K.subgroupOf P).Normal := by
    have hPnormF : P ≤ Subgroup.normalizer (F : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFN.1).mp hFN.2
    have hNormCentralizer : Subgroup.normalizer (F : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (F : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (F : Set G))).mp inferInstance
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    exact (le_inf P.le_normalizer (hPnormF.trans hNormCentralizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  apply le_antisymm (sup_le inf_le_left hSP)
  by_contra hnot
  have hcore := SectionThree.normal_inf_sylow_le_twoCore S h P K hP hsolv
    inf_le_left hKN hnot
  exact hTnot ((le_inf (le_inf (hTS.trans hSP) hTF) hTS).trans hcore)

private theorem fixed_vector_centralizer_generates
    {G : Type*} [Group G] [Finite G]
    (S P F T D : Subgroup G) (h : SectionThree.Hypotheses G S)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hFN : NormalIn F P) (hTS : T ≤ S)
    (hTF : T ≤ Subgroup.centralizer (F : Set G))
    (hTnot : ¬ T ≤ twoCoreAmbient P)
    (hSD : S ≤ D) (hDP : D ≤ P)
    (v : G) (hv : v ∈ F) :
    (P ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ D = P := by
  have hgen := fixed_normal_centralizer_generates S P F T h hP hsolv hFN hTS hTF hTnot
  apply le_antisymm (sup_le inf_le_left hDP)
  apply hgen.ge.trans
  exact sup_le_sup (inf_le_inf_left P (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))) hSD

public theorem eight_five_fixed_vector_centralizer_generation_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hnoncontain : ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hnormal : NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.firstStep))
    (v : H) (hv : v ∈ w.oneJFixedPoints S) :
    (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let T := twoCoreIn (EAt Γ cp.a)
  have hTQ : T ≤ q Γ cp.a := by
    change twoCoreIn (e Γ cp.a) ≤ q Γ cp.a
    rw [CosetGraphContext.e, Γ.twoResidualAt_def, q, Γ.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hTS : T ≤ S := hTQ.trans (local_cores_le_edge_sylow h Γ cp).1
  have hFZ : w.oneJFixedPoints S ≤ z Γ cp.a := Subgroup.map_subtype_le _
  have hZcentral : z Γ cp.a ≤ Subgroup.centralizer (q Γ cp.a : Set H) := by
    have hb : cp.firstStep ∈ neighborhood Γ cp.a :=
      (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
    exact ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hb).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hTF : T ≤ Subgroup.centralizer (w.oneJFixedPoints S : Set H) :=
    hTQ.trans ((Subgroup.le_centralizer_iff.mp hZcentral).trans
      (Subgroup.centralizer_le hFZ))
  have hTnot : ¬ T ≤ twoCoreAmbient (GAt Γ cp.firstStep) := by
    have hn := hnoncontain
    change ¬ T ≤ Γ.twoCoreAt cp.firstStep at hn
    rw [Γ.twoCoreAt_def] at hn
    exact hn
  exact fixed_vector_centralizer_generates S (GAt Γ cp.firstStep)
    (w.oneJFixedPoints S) T (GAt Γ cp.a ⊓ GAt Γ cp.firstStep)
    (sectionThreeHypotheses h)
    ((pFamily_iff_pSet _ _ _).mp (edge_local_data h Γ cp).2.1)
    (edge_local_data h Γ cp).2.2 hnormal hTS hTF hTnot
    cp.S_le_edge_stabilizers inf_le_right v hv

end Stellmacher.SectionEight

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- Fixed-vector centralizers generate the next stabilizer in the actual join. -/
public theorem generated_eight_five_fixed_vector_centralizer_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set (P1 ⊔ P2 : Subgroup H)))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hnormal : NormalIn (w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2)))
      (GAt ctx.Γ ctx.criticalPath.firstStep))
    (v : (P1 ⊔ P2 : Subgroup H))
    (hv : v ∈ w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2))) :
    (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set (P1 ⊔ P2 : Subgroup H))) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_five_fixed_vector_centralizer_generation_local ctx.toLocalContext
    (generated_lemma_eight_three ctx hcenter) w hnormal v hv

/-- Fixed-subgroup normality forces the generated initial center to have order four. -/
public theorem generated_eight_five_center_card_four_of_fixed_normal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set (P1 ⊔ P2 : Subgroup H)))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hnormal : NormalIn (w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2)))
      (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  have hfixedNext : w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2)) ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
    intro vector hvector
    exact generated_eight_four_vector_centralizer_criterion ctx hcenter w vector hvector
      (generated_eight_five_fixed_vector_centralizer_generation
        ctx hcenter w hnormal vector hvector)
  have hnextFix : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.centralizer
      (w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2)) : Set (P1 ⊔ P2 : Subgroup H)) :=
    Subgroup.le_centralizer_iff.mp
      (hfixedNext.trans (hcenter.trans (SevenSix.centerAmbient_le_centralizer _)))
  exact eight_five_center_card_four_of_sylow_centralizes_fixed_local
    ctx.toLocalContext hcenter w
    ((ctx.criticalPath.S_le_edge_stabilizers.trans inf_le_right).trans hnextFix)

end Stellmacher.SectionEight
