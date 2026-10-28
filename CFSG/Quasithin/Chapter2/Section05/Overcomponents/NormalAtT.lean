module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.PersistenceAtT
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.OuterPGroupSylowSupplement
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# The original centralizer supplement after K = K₀

The proved persistence theorem makes K a component of G_t. Its normalization
by the original Sylow and the SQTK rank bound force normality in G_t.
The proved two-group outer automizer supplies G_t = H C_{G_t}(K).
The source central-four splitting puts this centralizer inside C_G(z) ≤ M;
normal-subgroup inheritance from G_t ∩ M gives characteristic two.

These are the 2.5.18 inputs used after the genuine 2.5.20 conclusion K=K₀.
Normality in H remains explicit and belongs to that independent source proof.
The A₆ source centralizer consumer uses all three results.

Source: Aschbacher--Smith, 2.5.18, printed p.560, and 2.5.22, p.567.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection
variable {G:Type*} [Group G] [Finite G] {H K M:Subgroup G} {S:Sylow 2 H} {z:G}

/-- The original K is normal in G_t once source 2.5.20 has made it normal in H.
Source 2.5.18 supplies componenthood; the actual Sylow excludes the orbit of two. -/
theorem source_component_normal_in_centralizer_t
    (c:MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype)) :
    centralizer ({t}:Set G) ≤ normalizer (K:Set G) := by
  let J:=centralizer ({t}:Set G)
  have hc:=source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  obtain ⟨_,_,⟨P,hP⟩,_⟩:=MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hKN:H≤normalizer (K:Set G):=
    (normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance
  have hPN:(P:Subgroup J)≤normalizer (K.subgroupOf J:Set J):=by
    intro a ha b
    apply Iff.intro <;> intro h
    · exact (hKN (map_subtype_le _ (hP ▸ mem_map_of_mem J.subtype ha)) b).mp h
    · exact (hKN (map_subtype_le _ (hP ▸ mem_map_of_mem J.subtype ha)) b).mpr h
  have hn:(K.subgroupOf J).Normal:=
    hc.2.normal_of_sylow_normalizes_of_odd_rank_le_two
      (hG.involution_centralizer_sqtk ht).stronglyQuasithin P hPN
  exact (normal_subgroupOf_iff_le_normalizer hc.1).mp hn

/-- Source 2.5.18(2) after K=K₀: the actual G_t is H times its K-centralizer. -/
theorem source_normal_component_centralizer_supplement
    (c:MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype)) :
    centralizer ({t}:Set G)=H⊔(centralizer ({t}:Set G)⊓centralizer (K:Set G)) := by
  let J:=centralizer ({t}:Set G)
  obtain ⟨hHJ,_,⟨P,hP⟩,_⟩:=MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hKJ:K≤J:=c.component_le.trans hHJ
  let B:=K.subgroupOf J
  let : B.Normal:=(normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ)
  have ho:IsPGroup 2 (MulAut.Outer B):=
    (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.2.1.of_equiv
      (MulAut.outerCongr (subgroupOfEquivOfLe hKJ)).symm
  have hg:=congrArg (Subgroup.map J.subtype) (normal_centralizer_sup_sylow_eq_top B P ho)
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.map_centralizer_subtype,map_subgroupOf_eq_of_le hKJ,hP,
    ←MonoidHom.range_eq_map,range_subtype] at hg
  simpa only [hgen,sup_assoc,sup_comm,sup_left_comm] using hg.symm
/-- Source 2.5.18(2–3) after K=K₀: its literal centralizer lies in M and has
characteristic two. No centralizer-containment or characteristic-two premise is used. -/
theorem source_normal_component_centralizer_mem_He
    (c:MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype)) :
    (centralizer ({t}:Set G)⊓centralizer (K:Set G))≤M ∧
      (centralizer ({t}:Set G)⊓centralizer (K:Set G))∈Chapter1.He G := by
  let Y:=(S:Subgroup H).map H.subtype
  let J:=centralizer ({t}:Set G)
  let C:=J⊓centralizer (K:Set G)
  obtain ⟨hHJ,hJgamma,⟨P,hP⟩,_⟩:=MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hKJ:K≤J:=c.component_le.trans hHJ
  have hJN:=source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  obtain ⟨hs,hd,hcard,_⟩:=MathieuSourceSetup.normal_component_center_split c hG hempty hgen hb
  have hcc:Nat.card (centerIn Y⊓twoCore H:Subgroup G)=2:=
    (MathieuSourceSetup.center_four_of_center_split c hgen (centerIn Y⊓K) hs hd hcard).2
  have hline:centerIn Y⊓twoCore H=zpowers t:=by
    have hle:zpowers t≤centerIn Y⊓twoCore H:=zpowers_le.mpr ⟨htZ,htC⟩
    apply (eq_of_le_of_card_ge hle ?_).symm
    rw [hcc,Nat.card_zpowers,ht]
  have hzspan:z∈K⊔zpowers t:=by
    have hh:=c.localSetup hG structural115Input localC129Input_knownSimple
    have hzZ:z∈centerIn Y:=⟨hh.mem_sylow,hh.central⟩
    have hZ:centerIn Y≤K⊔zpowers t:=by
      rw [hs,hline]
      exact sup_le_sup inf_le_right le_rfl
    exact hZ hzZ
  have hCM:C≤M:=by
    intro a ha
    apply (c.localSetup hG structural115Input localC129Input_knownSimple).centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hsub:K⊔zpowers t≤centralizer ({a}:Set G):=by
      apply sup_le
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (ha.2 k hk)
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha.1).symm)
    exact (mem_centralizer_singleton_iff.mp (hsub hzspan)).symm
  have hJM:J⊓M∈Chapter1.He G:=lemma_2_3_9_4
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic c.T M c.maximal c.sylow_le))
    hJgamma (localPairsIn_mono hHJ c.pair) P (by rw [hP];exact c.base_le)
  have hCJM:C≤J⊓M:=le_inf inf_le_left hCM
  have hnormal:(C.subgroupOf (J⊓M)).Normal:=by
    apply (normal_subgroupOf_iff_le_normalizer hCJM).mpr
    exact (le_inf (inf_le_left.trans J.le_normalizer)
      (inf_le_left.trans (hJN.trans (normalizer_le_normalizer_centralizer K)))).trans
      inf_normalizer_le_normalizer_inf
  have hCne:C≠⊥:=by
    intro he
    have htmem:t∈C:=⟨mem_centralizer_singleton_iff.mpr rfl,fun k hk=>(mem_centralizer_singleton_iff.mp (hKJ hk))⟩
    have he1:t=1:=mem_bot.mp (he ▸ htmem)
    rw [he1,orderOf_one] at ht
    omega
  exact ⟨hCM,Chapter1.lemma_1_1_3_1 hJM hCne hCJM hnormal.isSubnormal⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
