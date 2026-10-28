module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BorelNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.Centralizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SylowStabilizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddMovement

/-!
# The proper common component of the general-field natural blocks

The actual half-Sylow restricts the original local family to the opposite
Borel normalizer. Unique C-component containment selects an overcomponent.
The original nonidentity odd Hall intersection generates the comparison
block by commutators, so subnormal absorption places it in the same
component. Its escape from the original maximal local proves strict
containment. The nonsolvable original block forces the overcomponent to
centralize the Borel. Both natural modules, full two-cores, trivial centers,
and the literal common Sylow survive restriction to this overcomponent.
The stronger constructor also retains the decomposition of the original
full module into the original block core and a submodule of the opposite
Borel Sylow, together with the comparison block’s escape from M.

The source application constructs all this data from natural marking and
original Hall placement. Its terminal consumer retains only the actual
SL₃ or PSL₃ model as an additional geometric premise. The task
qt-d-10-nona5-moving-hall-three owns that recognition and the remaining
natural marking and Hall placement; this is not yet NaturalTerminalAt.

Source: Aschbacher–Smith 10.2.3(4), printed p.747, using 1.2.4 and A.3.3.
Subnormal commutator absorption supplies the containment directly and uses
K = O²(K), never the false two-core identity K = O₂(K).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem factor_stabilizer_local
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) {J : Subgroup G}
    (hJ : J = L ∨ J = L.map (MulAut.conj t).toMonoidHom) :
    J ∈ Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  rcases hJ with rfl | rfl
  · exact Chapter1.Section02.mem_L_sylow_stabilizer D.maximal.1
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hRT : (R.subgroupOf (T : Subgroup G)).Normal := by
    have he : R.subgroupOf (T : Subgroup G) = (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact normal_of_index_eq_two
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp hRT
  have hm : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hTR ht)
  have hh := (Chapter1.mem_L_map_iff (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).mpr
    (Chapter1.Section02.mem_L_sylow_stabilizer D.maximal.1)
  rwa [hm] at hh

private theorem center_eq_bot_transport {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (h : center X = ⊥) : center Y = ⊥ := by
  apply bot_unique
  intro y hy
  have hh := (centerCongr a.symm ⟨y,hy⟩).property
  change a.symm y ∈ center X at hh
  rw [h,mem_bot] at hh
  exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))

private theorem core_eq_transport {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (h : pCore 2 X = blockU X) : pCore 2 Y = blockU Y := by
  rw [←pCore_map_iso 2 a,h,blockU,map_commutator,pCore_map_iso,
    map_top_of_surjective _ a.surjective,blockU]

private theorem odd_sylow_faithful (J P A : Subgroup G)
    (hJ : IsShort J) (hz : center J = ⊥) (hP : Chapter1.IsSylowIn 2 P J)
    (hAJ : A ≤ J) (hodd : Odd (Nat.card A)) : A ⊓ centralizer (P : Set G) = ⊥ := by
  let Q := A ⊓ centralizer (P : Set G)
  have hQJ : Q ≤ J := inf_le_left.trans hAJ
  have hQo : Odd (Nat.card Q) := hodd.of_dvd_nat (card_dvd_of_le (show Q ≤ A from inf_le_left))
  have hc := hJ.centralizes_of_odd_sylow_fixed J P Q hP hQo
    (hQJ.trans J.le_normalizer) inf_le_right
  apply bot_unique
  intro x hx
  have hh : (⟨x,hQJ hx⟩ : J) ∈ center J := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc hx y y.property)
  rw [hz,mem_bot] at hh
  exact mem_bot.mpr (congrArg J.subtype hh)

/-- Construct the proper centralizing component from either literal axis orientation. -/
theorem Context.common_component_of_aligned_axes
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (A J K Q : Subgroup G)
    (hAB : A ≤ B.map H.subtype) (hA : Nat.card A = 2^n-1)
    (hfactor : A ≤ L ∨ A ≤ L.map (MulAut.conj t).toMonoidHom)
    (hJ : J = L ∨ J = L.map (MulAut.conj t).toMonoidHom)
    (hJA : J ≤ centralizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G))
    (hKA : K ≤ centralizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G))
    (hout : ¬ K ≤ D.maximalLocal) (hKn : IsL2EvenBlock K n)
    (hQJ : Q ≤ J) (hQK : Q ≤ K) (hQB : Q ≤ B.map H.subtype) (hQne : Q ≠ ⊥) :
    IsSQTK KnownSimple.IsKnownSimple
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) ∧
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) ∧
    ∃! C : Subgroup G,
      C ∈ Chapter1.cComponentsIn
        (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) ∧
      J < C ∧ K ≤ C ∧
      C ≤ centralizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G) := by
  let A₀ := (⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G)
  let N := normalizer (A₀ : Set G)
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hKN : K ≤ N := hKA.trans (Subgroup.centralizer_le_normalizer _)
  have hJN : J ≤ N := hJA.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hP,hN⟩ := ctx.axis_borel_normalizer_sylow D n hn hF e mark hBB ht htn
    A K hAB hA hfactor hKN hout
  obtain ⟨P,hPm⟩ := hP
  have hRN : R ≤ N := by
    change (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ N
    rw [←hPm]
    exact map_subtype_le _
  have hPe : (P : Subgroup N) = R.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hPm,map_subgroupOf_eq_of_le hRN]
  have hlocal : J.subgroupOf N ∈ Chapter1.L N P := by
    rw [hPe]
    exact (Chapter1.mem_LIn_iff_subgroupOf hRN hJN).mp
      ⟨hJN,factor_stabilizer_local D ctx.nonnormal ht hJ⟩
  have hNQ : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  have hmove := hKn.odd_commutator_eq K Q hQK (ctx.odd_card_of_le_hall_image Q hQB) hQne
  obtain ⟨C,⟨hC,hJC,hKC,hCA⟩,hu⟩ :=
    source_natural_pair_common_centralizing_component A₀ J K Q hNQ P hlocal hJA hKN hQJ hmove
  have hJM : J ≤ D.maximalLocal := by
    rcases hJ with hJ | hJ
    · rw [hJ]
      exact (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
    · rw [hJ]
      have hLM : L ≤ D.maximalLocal :=
        (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
      have hm : D.maximalLocal.map (MulAut.conj t).toMonoidHom = D.maximalLocal :=
        mem_normalizer_iff_map_conj_eq.mp
          (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T ht))
      exact (map_mono hLM).trans_eq hm
  have hproper : J < C := lt_of_le_of_ne hJC (fun he => hout (hKC.trans (he ▸ hJM)))
  exact ⟨hN,⟨P,hPm⟩,C,⟨hC,hproper,hKC,hCA⟩,
    fun E hE => hu E ⟨hE.1,hE.2.1.le,hE.2.2.1,hE.2.2.2⟩⟩

/-- The actual proper common component, before its remaining model recognition.
All subgroup and Sylow fields retain the original ambient inclusions. -/
structure CommonOvercomponent (T : Sylow 2 G) (L H : Subgroup G)
    (B : Subgroup H) (n : ℕ) where
  axis : Subgroup G
  original : Subgroup G
  comparison : Subgroup H
  overcomponent : Subgroup G
  axis_le_hall : axis ≤ B.map H.subtype
  axis_original : axis ≤ L ∨ ∃ t : G, t ∈ T ∧
    t ∉ normalizer (L : Set G) ∧ axis ≤ L.map (MulAut.conj t).toMonoidHom
  axis_card : Nat.card axis = 2^n-1
  original_factor : original = L ∨ ∃ t : G, t ∈ T ∧
    t ∉ normalizer (L : Set G) ∧ original = L.map (MulAut.conj t).toMonoidHom
  original_natural : IsL2EvenBlock original n
  comparison_block : IsBlock comparison
  comparison_natural : IsL2EvenBlock comparison n
  original_core : pCore 2 original = blockU original
  comparison_core : pCore 2 comparison = blockU comparison
  original_center : center original = ⊥
  comparison_center : center comparison = ⊥
  hall_intersection_le_original : (B ⊓ comparison).map H.subtype ≤ original
  common_sylow_original : Chapter1.IsSylowIn 2
    ⁅baumann (T : Subgroup G),(B ⊓ comparison).map H.subtype⁆ original
  common_sylow_comparison : Chapter1.IsSylowIn 2
    ⁅baumann (T : Subgroup G),(B ⊓ comparison).map H.subtype⁆ (comparison.map H.subtype)
  faithful : axis ⊓ centralizer
    ((⁅baumann (T : Subgroup G),axis⁆ : Subgroup G) : Set G) = ⊥
  local_sqtk : IsSQTK KnownSimple.IsKnownSimple
    (normalizer ((⁅baumann (T : Subgroup G),axis⁆ ⊔ axis : Subgroup G) : Set G))
  normalizer_sylow : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
    (normalizer ((⁅baumann (T : Subgroup G),axis⁆ ⊔ axis : Subgroup G) : Set G))
  component : overcomponent ∈ Chapter1.cComponentsIn
    (normalizer ((⁅baumann (T : Subgroup G),axis⁆ ⊔ axis : Subgroup G) : Set G))
  original_lt : original < overcomponent
  comparison_le : comparison.map H.subtype ≤ overcomponent
  distinct : original ≠ comparison.map H.subtype
  centralizes : overcomponent ≤ centralizer
    ((⁅baumann (T : Subgroup G),axis⁆ ⊔ axis : Subgroup G) : Set G)
  local_family : ∃ P : Sylow 2 overcomponent,
    (P : Subgroup overcomponent) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf overcomponent ∧
    original.subgroupOf overcomponent ∈ localCComponents P ∧
    (comparison.map H.subtype).subgroupOf overcomponent ∈ localCComponents P

omit [Finite G] in
/-- The remaining model recognition is the sole additional input to the literal terminal consumer. -/
theorem CommonOvercomponent.terminal {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hmodel : Chapter1.Section02.LocalModels.IsSL c.overcomponent 3 (2^n) ∨
      ClassicalGroup.IsPSL c.overcomponent 3 (2^n)) :
    Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  have hAL : c.axis ≤ localOrbit T L := by
    rcases c.axis_original with h | ⟨t,ht,_,h⟩
    · exact h.trans (le_componentOrbit L T)
    · have hh := map_mono (f := (MulAut.conj t).toMonoidHom) (le_componentOrbit L T)
      have hm := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
      exact h.trans (hh.trans_eq hm)
  exact ⟨{
    axis := c.axis
    overcomponent := c.overcomponent
    axis_le_hall := c.axis_le_hall
    axis_le_orbit := hAL
    axis_original := c.axis_original
    axis_card := c.axis_card
    faithful := c.faithful
    local_sqtk := c.local_sqtk
    component := c.component
    model := hmodel
    centralizes := c.centralizes }⟩

/-- Construct the common component while retaining the original module split
and the comparison block’s escape from the original maximal local. -/
theorem Context.common_overcomponent_with_module
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    ∃ c : CommonOvercomponent T L H B n, ∃ U : Subgroup G,
      D.fullModule = (blockU c.original).map c.original.subtype ⊔ U ∧
      U ≤ ⁅baumann (T : Subgroup G),c.axis⁆ ∧
      ¬ c.comparison.map H.subtype ≤ D.maximalLocal := by
  obtain ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,hnatL,hcoreL,hzL,hborelL,hbK,hnatK,hcoreK,hzK,hSK,haxis,haxisS,
    t,ht,htn,a,hfirst,hsecond,hor,hA₁L,hA₂L,hcard₁,hcard₂,hdis,hjoin,hcy₁,hcy₂,hcommon,
    hop,hne,hcomm,hout⟩ := ctx.component_with_opposite_borel_geometry D n hn hF e mark hBB
  let S := baumann (T : Subgroup G)
  let J := L.map (MulAut.conj t).toMonoidHom
  let K₀ := K.map H.subtype
  let Q := (B ⊓ K).map H.subtype
  let C := B.map H.subtype
  let hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
  let f := (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))).comp (inclusion hCR)
  let A₁ := ((MonoidHom.snd _ _).comp f).ker.map C.subtype
  let A₂ := ((MonoidHom.fst _ _).comp f).ker.map C.subtype
  have hA₁ : Nat.card A₁ = 2^n-1 := hcard₁.trans (congrArg (fun q : ℕ => q-1) hF)
  have hA₂ : Nat.card A₂ = 2^n-1 := hcard₂.trans (congrArg (fun q : ℕ => q-1) hF)
  have hQcard : Nat.card Q = 2^n-1 := by
    rw [card_map_of_injective H.subtype_injective]
    exact hcard.trans (congrArg (fun q : ℕ => q-1) hF)
  have hnontrivial (V : Subgroup G) (hV : Nat.card V = 2^n-1) : V ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hV
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  let j : L ≃* J := (MulAut.conj t).subgroupMap L
  have hnatJ : IsL2EvenBlock J n := hnatL.of_mulEquiv j
  have hcoreJ : pCore 2 J = blockU J := core_eq_transport j hcoreL
  have hzJ : center J = ⊥ := center_eq_bot_transport j hzL
  have hnatK₀ : IsL2EvenBlock K₀ n := hnatK.of_mulEquiv (K.equivMapOfInjective H.subtype H.subtype_injective)
  have hQB : Q ≤ B.map H.subtype := map_mono inf_le_left
  have hQK : Q ≤ K₀ := map_mono inf_le_right
  have hLJ : L ≤ centralizer (J : Set G) :=
    source_original_block_commutes_prescribed_conjugate D hbL ht htn
  obtain ⟨hS₁,hP₁,_,_⟩ := hborelL A₁ hA₁L (map_subtype_le _) (hnontrivial A₁ hA₁)
  obtain ⟨hS₂,hP₂⟩ := ctx.original_conjugate_axis_sylow D n hn hF e mark hBB hbL ht
    A₂ hA₂L (map_subtype_le _) (hnontrivial A₂ hA₂)
  have hL₂ : L ≤ centralizer ((⁅S,A₂⁆ ⊔ A₂ : Subgroup G) : Set G) :=
    hLJ.trans (centralizer_le (sup_le (by rw [hS₂]; exact inf_le_right) hA₂L))
  have hJ₁ : J ≤ centralizer ((⁅S,A₁⁆ ⊔ A₁ : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp hLJ).trans (centralizer_le (sup_le (by rw [hS₁]; exact inf_le_right) hA₁L))
  have hUL : (blockU L).map L.subtype = ⁅D.fullModule,L⁆ :=
    source_original_blockU_eq_full_moved D hbL
  have hUJ : ((blockU L).map L.subtype).map (MulAut.conj t).toMonoidHom =
      (blockU J).map J.subtype := by
    have hh := congrArg (map J.subtype) (RankOne.Solvable.blockU_map_equiv j)
    rw [map_map] at hh ⊢
    have hf : J.subtype.comp j.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp L.subtype := by
      ext x
      rfl
    rw [hf] at hh
    exact hh
  have hfull : D.fullModule = (blockU L).map L.subtype ⊔ (blockU J).map J.subtype := by
    rw [←hUJ,hUL]
    apply source_nonnormal_fullModule_eq_moved_pair D ctx.nonnormal ht
    rw [←hUL]
    exact (map_mono (map_subtype_le _)).trans (le_centralizer_iff.mp hLJ)
  have hcore_sylow (I R : Subgroup G) (hc : pCore 2 I = blockU I)
      (hR : Chapter1.IsSylowIn 2 R I) : (blockU I).map I.subtype ≤ R := by
    obtain ⟨P,hP⟩ := hR
    rw [←hc,←hP]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal P)
  have hfaith₁ := odd_sylow_faithful L ⁅S,A₁⁆ A₁ hnatL.2.1 hzL hP₁ hA₁L
    (ctx.odd_card_of_le_hall_image A₁ (map_subtype_le _))
  have hfaith₂ := odd_sylow_faithful J ⁅S,A₂⁆ A₂ hnatJ.2.1 hzJ hP₂ hA₂L
    (ctx.odd_card_of_le_hall_image A₂ (map_subtype_le _))
  have hKR : K₀ ∈ localCComponents ((T : Subgroup G) ⊓ normalizer (L : Set G)) := by
    apply cComponent_mem_localCComponents (H := H) _ (map_subtype_le _) (inf_le_left.trans ctx.hstar.1.1.2)
    have he : K₀.subgroupOf H = K := by
      change (K.map H.subtype).comap H.subtype = K
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rwa [he]
  have assemble (A I : Subgroup G)
      (hIA : I = L ∨ I = J) (hAf : A ≤ L ∨ A ≤ J)
      (hAB : A ≤ B.map H.subtype) (hA : Nat.card A = 2^n-1)
      (hIn : IsL2EvenBlock I n) (hIc : pCore 2 I = blockU I) (hIz : center I = ⊥)
      (hQI : Q ≤ I) (hPI : Chapter1.IsSylowIn 2 ⁅S,Q⁆ I)
      (hfaith : A ⊓ centralizer ((⁅S,A⁆ : Subgroup G) : Set G) = ⊥)
      (hIAc : I ≤ centralizer ((⁅S,A⁆ ⊔ A : Subgroup G) : Set G))
      (hKAc : K₀ ≤ centralizer ((⁅S,A⁆ ⊔ A : Subgroup G) : Set G))
      (U : Subgroup G) (hfull : D.fullModule = (blockU I).map I.subtype ⊔ U)
      (hUS : U ≤ ⁅S,A⁆) :
      ∃ c : CommonOvercomponent T L H B n, ∃ U : Subgroup G,
        D.fullModule = (blockU c.original).map c.original.subtype ⊔ U ∧
        U ≤ ⁅baumann (T : Subgroup G),c.axis⁆ ∧
        ¬ c.comparison.map H.subtype ≤ D.maximalLocal := by
    obtain ⟨hN,hPN,Cp,⟨hC,hIC,hKC,hCA⟩,hu⟩ := ctx.common_component_of_aligned_axes D n hn hF e mark hBB
      ht htn A I K₀ Q hAB hA hAf hIA hIAc hKAc hout hnatK₀ hQI hQK hQB (hnontrivial Q hQcard)
    have hIR := factor_stabilizer_local D ctx.nonnormal ht hIA
    obtain ⟨P,hPm⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hPN hC.1 hC.2.subnormal
    have hPe : (P : Subgroup Cp) = ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf Cp := by
      apply map_injective Cp.subtype_injective
      rw [hPm,subgroupOf_map_subtype]
    have hIM : I ≤ D.maximalLocal := by
      rcases hIA with hIA | hIA
      · rw [hIA]
        exact (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
      · rw [hIA]
        have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
        have hm : D.maximalLocal.map (MulAut.conj t).toMonoidHom = D.maximalLocal :=
          mem_normalizer_iff_map_conj_eq.mp
            (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T ht))
        exact (map_mono hLM).trans_eq hm
    refine ⟨{
      axis := A
      original := I
      comparison := K
      overcomponent := Cp
      axis_le_hall := hAB
      axis_original := hAf.imp id (fun h => ⟨t,ht,htn,h⟩)
      axis_card := hA
      original_factor := hIA.imp id (fun h => ⟨t,ht,htn,h⟩)
      original_natural := hIn
      comparison_block := hbK
      comparison_natural := hnatK
      original_core := hIc
      comparison_core := hcoreK
      original_center := hIz
      comparison_center := hzK
      hall_intersection_le_original := hQI
      common_sylow_original := hPI
      common_sylow_comparison := haxisS
      faithful := hfaith
      local_sqtk := hN
      normalizer_sylow := hPN
      component := hC
      original_lt := hIC
      comparison_le := hKC
      distinct := fun he => hout (he ▸ hIM)
      centralizes := hCA
      local_family := ⟨P,hPe,?_,?_⟩ },U,hfull,hUS,hout⟩
    · rw [hPe]
      exact SourceEmbeddings.local_restrict hIR.1 hIC.le
    · rw [hPe]
      exact SourceEmbeddings.local_restrict hKR hKC
  rcases hop with ⟨hQ,hopp⟩ | ⟨hQ,hopp⟩
  · exact assemble A₂ L (Or.inl rfl) (Or.inr hA₂L) (map_subtype_le _) hA₂
      hnatL hcoreL hzL (hQ.le.trans hA₁L) (by
        change Chapter1.IsSylowIn 2 ⁅S,(B ⊓ K).map H.subtype⁆ L
        rw [hQ]
        exact hP₁) hfaith₂ hL₂ (le_centralizer_iff.mp hopp)
      ((blockU J).map J.subtype) hfull (hcore_sylow J _ hcoreJ hP₂)
  · exact assemble A₁ J (Or.inr rfl) (Or.inl hA₁L) (map_subtype_le _) hA₁
      hnatJ hcoreJ hzJ (hQ.le.trans hA₂L) (by
        change Chapter1.IsSylowIn 2 ⁅S,(B ⊓ K).map H.subtype⁆ J
        rw [hQ]
        exact hP₂) hfaith₁ hJ₁ (le_centralizer_iff.mp hopp)
      ((blockU L).map L.subtype) (hfull.trans (sup_comm _ _))
      (hcore_sylow L _ hcoreL hP₁)


/-- Natural marking and original Hall placement construct the original common component. -/
theorem Context.common_overcomponent
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    Nonempty (CommonOvercomponent T L H B n) := by
  obtain ⟨c,_⟩ := ctx.common_overcomponent_with_module D n hn hF e mark hBB
  exact ⟨c⟩

end CFSG.Quasithin.Chapter10.MovingHall
