module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Full
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.ConjugateSpan
public import Theory.GroupTheory.PResidual.NontrivialImage
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection

/-!
# Proper chosen supports in the Omega overgroup comparison

If N is a third maximal two-local, the proper source choice has
[M : M∩Mc]=3 and M=(M∩N)(M∩Mc). Since M∩Mc normalizes its two-core,
its whole M-conjugate span, and hence the literal residual Y, lie in M∩N.
The full-image uniqueness clause of 15.2.3 then forces the cubic row.

The cubic residual escapes Mc, so N=Y(N∩Mc). Consequently the partner
residual Y₂=O²(⟨O₂(N∩Mc)^N⟩) lies in Y. Genuine local core growth and the
reduced action make Y₂ noncentral on V(N). Ordering puts O₂(Y) in its
action kernel, so Y₂ covers Y/O₂(Y), which has order three. Normality and
two-perfectness give Y₂=Y. The nontrivial two-core identifies N_G(Y)=M,
contradicting N≠M. Combining this with the full-module comparison proves
original 15.2.5 for every chosen Omega support.

Source: Aschbacher--Smith 15.2.5, printed pp.1107--1108.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

/-- The literal proper choice retains the source index three. -/
theorem ChosenSmallSource.proper_partner_index
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M) : (M ⊓ Mc).relIndex M = 3 := by
  let := localModule_elementary_from_source h.ambient T
    ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1,h.maximal.1.2⟩
  have hc : V = localModule T M ∨
      ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
        SourceCases.Proper T M Mc (localModule T M)
          (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
        V = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype := h.chosen
  rcases hc with he | ⟨U,hU,_⟩
  · exact (hne he).elim
  · exact hU.2.2.2.2.2.2.2.2.2.2.1

/-- The original residual lies in the third intersection. -/
theorem ChosenSmallSource.proper_third_residual_le
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    h.residual ≤ M ⊓ N := by
  let := h.prepared.elementary
  have ho := h.omega_of_proper hne
  let H := M ⊓ N
  let B := M ⊓ Mc
  let R := B.pCoreIn 2
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hout : ¬ H ≤ B := fun he =>
    (h.prepared.third_maximal_action_constraints h.ambient T h.empty h.maximal
      h.centralizing h.partner hN hNM hNMc).1 (he.trans inf_le_right)
  have hprod : (H : Set G) * (B : Set G) = M :=
    coe_mul_eq_of_index_three_sylow T (le_inf h.maximal.1.2 hN.2)
      (le_inf h.maximal.1.2 hTMc) inf_le_left inf_le_left (h.proper_partner_index hne) hout
  have hRT : R ≤ (T : Subgroup G) := intersectionCore_le_sylow M Mc T h.maximal.1.2 hTMc
  have hBR : B ≤ normalizer (R : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hspan : conjugateSpanBy R M ≤ H := by
    apply (closure_le _).mpr
    rintro _ ⟨m,hm,r,hr,rfl⟩
    have hm' : m ∈ (H : Set G) * (B : Set G) := by rw [hprod]; exact hm
    obtain ⟨a,ha,b,hb,rfl⟩ := hm'
    have hc : b*r*b⁻¹ ∈ R := le_normalizer_iff.mp hBR b hb r hr
    have he : (a*b)*r*(a*b)⁻¹ = a*(b*r*b⁻¹)*a⁻¹ := by group
    rw [he]
    exact H.mul_mem (H.mul_mem ha ⟨h.maximal.1.2 (hRT hc),hN.2 (hRT hc)⟩) (H.inv_mem ha)
  change caseIIResidual T M (chosenStarredPreimage M V h.prepared.normalized) Mc ≤ H
  rw [source_omega_caseIIResidual_eq T h.maximal.1.2 h.prepared.normalized ho]
  exact (map_subtype_le _).trans hspan


omit [Finite G] in
private theorem normal_prime_index_supplement
    {Y B M : Subgroup G} (hYM : Y ≤ M) (hBM : B ≤ M)
    (hn : M ≤ normalizer (Y : Set G)) (hi : (B.relIndex M).Prime)
    (hout : ¬ Y ≤ B) : (Y : Set G) * (B : Set G) = M := by
  have hsup : Y ⊔ B = M := by
    have he := relIndex_mul_relIndex B (Y ⊔ B) M le_sup_right (sup_le hYM hBM)
    have hp : (B.relIndex (Y ⊔ B) * (Y ⊔ B).relIndex M).Prime := he.symm ▸ hi
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hrel⟩ | ⟨_,hrel⟩
    · exact (sup_le hYM hBM).antisymm (relIndex_eq_one.mp hrel)
    · exact (hout (le_sup_left.trans (relIndex_eq_one.mp hrel))).elim
  rw [←coe_mul_of_right_le_normalizer_left Y B (hBM.trans hn),hsup]

/-- A third overgroup forces the cubic source residual row. -/
theorem ChosenSmallSource.proper_third_residual_cubic
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    Nat.card (h.residual ⧸ pCore 2 h.residual) = 3 ∧
      h.residual ⊓ centralizer (V : Set G) = h.residual.pCoreIn 2 ∧
      ¬ h.residual ≤ Mc := by
  let := h.prepared.elementary
  have ho := h.omega_of_proper hne
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  have hle := h.proper_third_residual_le hne hN hNM hNMc
  have hnotfull : (h.residual.subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict ≠
        pResidual 2 (actionHom M V h.prepared.normalized).range := by
    intro he
    have hu := hs.unique_of_full_image he
    have ht : N ∈ maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) :=
      ⟨hN.1,sup_le (hle.trans inf_le_right) hN.2⟩
    rw [hu] at ht
    exact hNM (Set.mem_singleton_iff.mp ht)
  rcases hs.alternatives with hf | hf | hc
  · exact (hnotfull hf.1).elim
  · exact (hnotfull hf.1).elim
  obtain ⟨hm,hYne,_,hker⟩ := h.omega_cubic_residual_selection ho hc.1
  exact ⟨(Nat.card_congr hc.2.2.2.2.1.some.toEquiv).trans (by simp),hker,
    h.residual_subgroup_not_le_partner le_rfl h.residual_perfect hYne hm⟩

/-- The original residual supplements the third partner intersection. -/
theorem ChosenSmallSource.proper_third_factorization
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    (h.residual : Set G) * ((N ⊓ Mc : Subgroup G) : Set G) = N := by
  let := h.prepared.elementary
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared (h.omega_of_proper hne)
  have hle := h.proper_third_residual_le hne hN hNM hNMc
  have hout := (h.proper_third_residual_cubic hne hN hNM hNMc).2.2
  have hn : M ≤ normalizer (h.residual : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hle.trans inf_le_left)).mp hs.normal
  have hprod := normal_prime_index_supplement (hle.trans inf_le_left)
    (show M ⊓ Mc ≤ M from inf_le_left) hn
    (by rw [h.proper_partner_index hne]; exact Nat.prime_three)
    (fun hl => hout (hl.trans inf_le_right))
  have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing N hN
  apply Set.Subset.antisymm
  · rintro _ ⟨y,hy,b,hb,rfl⟩
    exact N.mul_mem (hle hy).2 hb.1
  · intro n hnN
    obtain ⟨a,ha,c,hc,rfl⟩ := hord n hnN
    have ha' : a ∈ (h.residual : Set G) * ((M ⊓ Mc : Subgroup G) : Set G) := by
      rw [hprod]; exact ha.2
    obtain ⟨y,hy,b,hb,he⟩ := ha'
    have hbN : b ∈ N := by
      have heq : b = y⁻¹*a := by rw [←he]; group
      rw [heq]
      exact N.mul_mem (N.inv_mem (hle hy).2) ha.1
    refine ⟨y,hy,b*c,⟨N.mul_mem hbN hc.1,
      Mc.mul_mem hb.2 (localModule_centralizer_le_partner T N h.partner hc.2)⟩,?_⟩
    change y*(b*c) = a*c
    change y*b = a at he
    rw [←mul_assoc,he]

/-- The third partner residual lies in the original cubic residual. -/
theorem ChosenSmallSource.proper_third_partner_residual_le
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    sourceResidual N Mc ≤ h.residual := by
  let Y := h.residual
  let R := (N ⊓ Mc).pCoreIn 2
  have hle := h.proper_third_residual_le hne hN hNM hNMc
  have hprod := h.proper_third_factorization hne hN hNM hNMc
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hRT : R ≤ (T : Subgroup G) := intersectionCore_le_sylow N Mc T hN.2 hTMc
  have hBR : N ⊓ Mc ≤ normalizer (R : Set G) := (N ⊓ Mc).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (N ⊓ Mc) (pCore 2 (N ⊓ Mc : Subgroup G)))
  have hspan : conjugateSpanBy R N = conjugateSpanBy R Y := by
    apply le_antisymm ?_ (conjugateSpanBy_mono le_rfl (hle.trans inf_le_right))
    apply (closure_le _).mpr
    rintro _ ⟨n,hn,r,hr,rfl⟩
    have hn' : n ∈ (Y : Set G) * ((N ⊓ Mc : Subgroup G) : Set G) := by
      rw [hprod]; exact hn
    obtain ⟨y,hy,b,hb,rfl⟩ := hn'
    exact subset_closure ⟨y,hy,b*r*b⁻¹,le_normalizer_iff.mp hBR b hb r hr,by group⟩
  have hRN : R ≤ N := (pCoreIn_le 2 _).trans inf_le_left
  have hnormal : (normalClosure (R.subgroupOf N : Set N)).map N.subtype =
      conjugateSpanBy R N := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy R N hRN,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hRN)]
  have he : sourceResidual N Mc = twoResidualAmbient (conjugateSpanBy R Y) := by
    change (twoResidualAmbient (normalClosure (R.subgroupOf N : Set N))).map N.subtype = _
    rw [map_twoResidualAmbient_of_subgroup_image _ _ _ hnormal,hspan]
  rw [he,residual_notation]
  exact embedded_residual_conjugateSpanBy_le R Y (isPGroup_pCoreIn 2 _)
    (hRT.trans h.residual_invariant)


/-- Core growth makes the literal partner residual act nontrivially on V(N). -/
theorem local_partner_residual_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) (hne : N ≠ Mc) :
    ¬ sourceResidual N Mc ≤ centralizer (localModule T N : Set G) := by
  let V := localModule T N
  let R := (N ⊓ Mc).pCoreIn 2
  let J := normalClosure (R.subgroupOf N : Set N)
  have hred := localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let := hred.normal
  let C := centralizer (V.subgroupOf N : Set N)
  let f := QuotientGroup.mk' C
  have hVle : V ≤ N := localModule_le T hN.2
  have hRle : R ≤ N := (pCoreIn_le 2 _).trans inf_le_left
  have hnot : ¬ R ≤ centralizer (V : Set G) :=
    (local_partner_core_inputs hG T hempty hN hu hmany hne).2.1
  have hJ : J.map f ≠ ⊥ := by
    intro he
    have hk : J ≤ C := by
      have hh := (Subgroup.map_eq_bot_iff _).mp he
      simpa only [f,QuotientGroup.ker_mk'] using hh
    apply hnot
    intro r hr v hv
    exact congrArg N.subtype (hk (subset_normalClosure
      (show (⟨r,hRle hr⟩ : N) ∈ R.subgroupOf N from hr)) ⟨v,hVle hv⟩ hv)
  have hneR := embedded_pResidual_image_ne_bot_of_pCore_eq_bot 2 J f
    (QuotientGroup.mk'_surjective C) hred.quotient_pCore_eq_bot hJ
  intro hc
  apply hneR
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  intro x hx v hv
  have hxY : (x:G) ∈ sourceResidual N Mc := by
    change (x:G) ∈ (twoResidualAmbient J).map N.subtype
    rw [residual_notation]
    exact mem_map_of_mem N.subtype hx
  exact Subtype.ext (hc hxY v hv)

/-- Both literal source residuals coincide in the proper-support branch. -/
theorem ChosenSmallSource.proper_third_residual_eq
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    sourceResidual N Mc = h.residual := by
  let := h.prepared.elementary
  let Y := h.residual
  let K := sourceResidual N Mc
  have hle := h.proper_third_residual_le hne hN hNM hNMc
  have hKY : K ≤ Y := h.proper_third_partner_residual_le hne hN hNM hNMc
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared (h.omega_of_proper hne)
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hle.trans inf_le_left)).mp hs.normal
  have hQ : Y.pCoreIn 2 ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 Y) ((pCoreIn_le 2 Y).trans (hle.trans inf_le_left))
    (hMY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
  have hQM : M.pCoreIn 2 ≤ centralizer (localModule T M : Set G) := by
    rw [←(local_partner_core_inputs h.ambient T h.empty h.maximal.1 h.partner h.many h.different).1]
    exact inf_le_right
  have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing N hN
  have hCN := (lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source h.ambient T hN)
  have hQC : Y.pCoreIn 2 ≤ centralizer (localModule T N : Set G) :=
    (le_inf ((pCoreIn_le 2 Y).trans (hle.trans inf_le_left)) (hQ.trans hQM)).trans
      (hCN.trans inf_le_right)
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 3 :=
    (h.proper_third_residual_cubic hne hN hNM hNMc).1
  let : Fact (Nat.card (Y ⧸ pCore 2 Y)).Prime := ⟨hc ▸ Nat.prime_three⟩
  have him : (K.subgroupOf Y).map q = ⊤ := by
    apply ((K.subgroupOf Y).map q).eq_bot_or_eq_top_of_prime_card.resolve_left
    intro he
    have hk : K.subgroupOf Y ≤ pCore 2 Y := by
      have hh := (Subgroup.map_eq_bot_iff _).mp he
      simpa only [q,QuotientGroup.ker_mk'] using hh
    apply local_partner_residual_noncentral h.ambient T h.empty hN h.partner h.many hNMc
    intro k hkK
    exact hQC (mem_map_of_mem Y.subtype
      (hk (show (⟨k,hKY hkK⟩ : Y) ∈ K.subgroupOf Y from hkK)))
  have hsup : K.subgroupOf Y ⊔ pCore 2 Y = ⊤ := by
    have hh := congrArg (comap q) him
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  have hNK : N ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le N Mc)).mp (residualY_normal N Mc)
  let : (K.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer
    ((hle.trans inf_le_right).trans hNK)
  have hp : IsPPerfect 2 (⊤ : Subgroup Y) := h.residual_perfect.of_surjective
    (Subgroup.topEquiv (G := Y)).symm.toMonoidHom (Subgroup.topEquiv (G := Y)).symm.surjective
  have ht := le_normal_of_isPPerfect_of_le_sup_pGroup (⊤ : Subgroup Y)
    (K.subgroupOf Y) (pCore 2 Y) hp pCore_isPGroup (by rw [hsup])
  apply le_antisymm hKY
  intro y hy
  exact ht (show (⟨y,hy⟩ : Y) ∈ (⊤ : Subgroup Y) from mem_top _)

/-- The residual normalizer rules out a third maximal overgroup. -/
theorem ChosenSmallSource.omega_proper_no_third_maximal
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) : False := by
  let := h.prepared.elementary
  let Y := h.residual
  have hle := h.proper_third_residual_le hne hN hNM hNMc
  have hYM : Y ≤ M := hle.trans inf_le_left
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared (h.omega_of_proper hne)
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp hs.normal
  obtain ⟨_,hker,hout⟩ := h.proper_third_residual_cubic hne hN hNM hNMc
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hcent : Y ≤ centralizer (V : Set G) := by
      have hcomm : ⁅V,Y⁆ ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
        ((IsElementaryAbelian.isPGroup 2 V).to_le
          (le_normalizer_iff_commutator_le_left.mp (hYM.trans h.prepared.normalized)))
        (le_normalizer_iff_commutator_le_right.mp (h.prepared.le_selected.trans hMY))
        (normalizer_commutator_ge_right V Y)
      have hb : ⁅V,Y⁆ = ⊥ := bot_unique (he ▸ hcomm)
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)
    have hy : Y = ⊥ := (inf_eq_left.mpr hcent).symm.trans (hker.trans he)
    apply hout
    change Y ≤ Mc
    rw [hy]
    exact bot_le
  have hnorm : normalizer (Y : Set G) = M :=
    normalizer_eq_of_nontrivial_core M Y (Y.pCoreIn 2) hYM h.maximal.1.1 hs.normal hcore le_rfl
  have he := h.proper_third_residual_eq hne hN hNM hNMc
  have hNK : N ≤ normalizer (Y : Set G) := by
    change sourceResidual N Mc = Y at he
    rw [←he]
    exact (normal_subgroupOf_iff_le_normalizer (sourceResidual_le N Mc)).mp (residualY_normal N Mc)
  rw [hnorm] at hNK
  exact hNM (le_antisymm hNK (hN.1.2 h.maximal.1.1.1 hNK))

/-- Original 15.2.5 in every chosen Omega row, including proper supports. -/
theorem ChosenSmallSource.maximal_overgroups_of_omega
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  classical
  by_cases hfull : V = localModule T M
  · exact h.maximal_overgroups_of_full_omega ho hfull
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    by_cases hNMc : N = Mc
    · simp [hNMc]
    exact (h.omega_proper_no_third_maximal hfull hN hNM hNMc).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact h.maximal.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩

end CFSG.Quasithin.Chapter15.Section02
