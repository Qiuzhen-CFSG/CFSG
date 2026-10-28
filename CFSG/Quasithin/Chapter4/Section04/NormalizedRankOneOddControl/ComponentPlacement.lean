module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Configurations
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.OddCentralizer
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer
public import Theory.GroupTheory.PerfectNormalizerInner.SimpleSection
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Theory.Quasithin.CoprimeRank

/-!
# Normal component placement with the original section kernel

The section-centralizer identity makes the commutator of the fixed residual
with the selected component centralizer a normal two-subgroup of that
centralizer. Its two-core is trivial. Residual uniqueness then rules out
involutions in the centralizer, makes the component normal, and places the
perfect residual in it. This argument retains central covers of L/O₂(L).

The residual's actual simple quotient and its solvable kernel convert a
model-specific outer-section exclusion to inner action. The resulting
component contains the original module and has a genuine section isomorphic
to that quotient. Its odd center preserves the module's two-rank.
Residual uniqueness and the outer-section exclusion remain explicit inputs;
this module does not assert the final odd-normalizer containment.
Source: Aschbacher--Smith, Remark 4.4.2 and 4.4.10--11, pp.619,621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G]

theorem component_centralizer_odd_of_section_kernel
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (hsection : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (hout:¬normalizer (A:Set G)≤normalizer (L:Set G))
    (K:Subgroup (normalizer (A:Set G))) (hK:IsComponent (normalizer (A:Set G)) K)
    (houtK:¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G))
    (hVK:V≤K.map (normalizer (A:Set G)).subtype) :
    Odd (Nat.card (centralizer (K:Set (normalizer (A:Set G))))) := by
  let N:=normalizer (A:Set G)
  let F:=oddActorResidual L A
  let J:=K.map N.subtype
  let C0:=centralizer (K:Set N)
  let C:=C0.map N.subtype
  have hFN:F≤N:=((oddActorResidual_le L A).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hCJ:C≤centralizer (J:Set G):=by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (hx y hy)
  have hCV:C≤centralizer (V:Set G):=hCJ.trans (centralizer_le hVK)
  have hCM:C≤normalizer (L:Set G):=hCV.trans ((Subgroup.centralizer_le_normalizer _).trans
    (oddNormalizer_reduction_of_cover_uniqueness D A hunique hout).1)
  have hCN:C≤N:=map_subtype_le _
  have hCF:C≤normalizer (F:Set G):=(le_inf hCM hCN).trans (normalizes_oddActorResidual L A)
  obtain ⟨_,hFK,_⟩:=chosen_oddNormalizer_component_normalization h D A hAN hcomm hodd hAV K hK
  have hFC:F≤normalizer (C:Set G):=by
    have hh:=(map_mono (f:=N.subtype) (hFK.trans (normalizer_le_normalizer_centralizer K))).trans
      (Subgroup.le_normalizer_map N.subtype)
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  have hcore:pCore 2 C0=⊥:=hK.centralizer_pCore_eq_bot_of_pCore_eq_bot 2
    (oddNormalizer_reduction_of_cover_uniqueness D A hunique hout).2
  have hcoreC:pCore 2 C=⊥:=by
    have he:=pCore_map_iso 2 (C0.equivMapOfInjective N.subtype N.subtype_injective)
    rw [hcore,Subgroup.map_bot] at he
    exact he.symm
  have hcommLC : ⁅L,C⁆ ≤ L.pCoreIn 2 := by
    rw [commutator_comm]
    exact ((le_sectionCentralizer_iff C L).mp ((le_inf hCM hCV).trans hsection)).2
  have hcommFC : ⁅F,C⁆ = ⊥ := by
    have hp : IsPGroup 2 (⁅F,C⁆ : Subgroup G) := (isPGroup_pCoreIn 2 L).to_le
      ((commutator_mono ((oddActorResidual_le L A).trans inf_le_left) le_rfl).trans hcommLC)
    have hh := le_pCoreIn_of_normalizes hp
      (le_normalizer_iff_commutator_le_right.mp hFC) (normalizer_commutator_ge_right F C)
    rw [pCoreIn,hcoreC,Subgroup.map_bot] at hh
    exact le_bot_iff.mp hh
  have hFCent:F≤centralizer (C:Set G):=commutator_eq_bot_iff_le_centralizer.mp hcommFC
  have hcOdd:Odd (Nat.card C):=by
    apply Nat.not_even_iff_odd.mp
    intro heven
    let :Fintype C:=Fintype.ofFinite C
    obtain ⟨c,hc⟩:=exists_prime_orderOf_dvd_card (G:=C) 2 (by
      simpa only [Nat.card_eq_fintype_card] using even_iff_two_dvd.mp heven)
    have hpow:(c:G)^2=1:=by
      have hh:=pow_orderOf_eq_one c
      rw [hc] at hh
      exact congrArg Subtype.val hh
    have hp:IsPGroup 2 (zpowers (c:G)):=
      (IsElementaryAbelian.zpowers_of_pow_eq_one (p:=2) hpow).isPGroup 2 _
    have hn:zpowers (c:G)≠⊥:=by
      intro hb
      have hh:(c:G)=1:=mem_bot.mp (hb ▸ mem_zpowers (c:G))
      have hh':c=1:=Subtype.ext hh
      rw [hh',orderOf_one] at hc
      omega
    have hz:zpowers (c:G)≤C:=zpowers_le.mpr c.property
    have hNZ:=normalizer_le_of_unique_maximalTwoLocal hunique.2.2 hp hn
      ((hFCent.trans (centralizer_le hz)).trans (Subgroup.centralizer_le_normalizer _))
    exact houtK (((le_centralizer_iff.mp hCJ).trans (centralizer_le hz)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNZ))
  exact (Nat.card_congr (C0.equivMapOfInjective N.subtype N.subtype_injective).toEquiv).symm ▸ hcOdd

/-- The solvable kernel of the actual simple quotient gives inner placement,
without removing the center of the original core quotient. -/
private theorem perfect_actor_inner_of_core_central_quotient
    {N S : Type*} [Group N] [Finite N] [Group S] [IsSimpleGroup S]
    (K F : Subgroup N) [Group.IsPerfect F]
    (e : ((F ⧸ pCore 2 F) ⧸ center (F ⧸ pCore 2 F)) ≃* S)
    (hno : ∀ U : Subgroup (MulAut.Outer K), ∀ f : U →* S, ¬ Function.Surjective f)
    (hn : F ≤ normalizer (K : Set N)) : F ≤ K ⊔ centralizer (K : Set N) := by
  let q := QuotientGroup.mk' (pCore 2 F)
  let z := QuotientGroup.mk' (center (F ⧸ pCore 2 F))
  let f : F →* S := e.toMonoidHom.comp (z.comp q)
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hk : f.ker = centralPreimage (pCore 2 F) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
    rfl
  let : Group.IsSolvable f.ker := hk ▸ centralPreimage_pCore_isSolvable 2
  exact perfect_le_sup_centralizer_of_no_simple_outer_section K F f hf hno hn

/-- Source 4.4.10--11 with the section kernel from Remark 4.4.2.
Only the residual's actual inner action remains an explicit model input. -/
theorem normal_component_of_inner_action
    {κ : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hsection : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hi : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G)))) :
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) := by
  have hv := chosen_oddNormalizer_module_le_of_component_inner_action
    h D A hAN hcomm hodd hAV hu K houtK hi
  have ho := component_centralizer_odd_of_section_kernel h D hsection
    A hAN hcomm hodd hAV hu hout K hK houtK hv
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFN).symm.surjective
  have hFK : F ≤ K.map N.subtype := by
    have hh := map_mono (f := N.subtype)
      (hK.perfect_actor_le_of_odd_centralizer ho (F.subgroupOf N) hi)
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  exact ⟨hK.normal_of_odd_centralizer ho,hv,hFK,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho⟩


private def centerQuotientCongr {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem module_rank_le_component_quotient
    (A V : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hv : V ≤ K.map (normalizer (A : Set G)).subtype)
    (ho : Odd (Nat.card (centralizer (K : Set (normalizer (A : Set G)))))) :
    primeRank 2 V ≤ primeRank 2 (K ⧸ center K) := by
  let N := normalizer (A : Set G)
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := ho.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  have hVR : primeRank 2 V ≤ primeRank 2 K := by
    have hh := primeRank_mono 2 hv
    rwa [← primeRank_equiv 2 (K.equivMapOfInjective N.subtype N.subtype_injective)] at hh
  exact hVR.trans (primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center K)) (by
    rw [QuotientGroup.ker_mk']
    exact hoZ.coprime_two_left))

/-- The constructed normal-component output of 4.4.10--11, with the
original residual and an actual simple section of the central quotient. -/
@[expose] def NormalComponentCase (L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      primeRank 2 V ≤ primeRank 2 (K ⧸ center K) ∧
      ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

/-- A residual with its literal core-central quotient supplies a normal
component and a section of that component's central quotient. The only
model input concerns sections of the outer automorphism group. -/
theorem normal_component_of_unique_and_no_outer_sections
    {S : Type*} [Group S] [IsSimpleGroup S]
    {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : 8 < Nat.card V)
    (hsection : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (e : ((oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ⧸
      center (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A))) ≃* S)
    (hno : ∀ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K →
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) →
      ∀ U : Subgroup (MulAut.Outer K), ∀ f : U →* S, ¬ Function.Surjective f) :
    NormalComponentCase L V A S := by
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,hFK,_⟩ :=
    component_of_unique h D hcard A hne hAN hcomm hodd hAV hu hout
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let u : F.subgroupOf N ≃* F := subgroupOfEquivOfLe hFN
  let eF : ((F.subgroupOf N ⧸ pCore 2 (F.subgroupOf N)) ⧸
      center (F.subgroupOf N ⧸ pCore 2 (F.subgroupOf N))) ≃* S :=
    (centerQuotientCongr (QuotientGroup.congr _ _ u (pCore_map_iso 2 u))).trans e
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := u.symm.toMonoidHom) u.symm.surjective
  have hi := perfect_actor_inner_of_core_central_quotient K (F.subgroupOf N)
    eF (hno K hK hmodel) hFK
  obtain ⟨hn,hv,hf,hcent⟩ := normal_component_of_inner_action
    h D hsection A hAN hcomm hodd hAV hu hout K hK houtK hi
  have ho : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine ⟨K,hK,hn,hm,houtK,hcore,hmodel,hv,hf,hcent,
    module_rank_le_component_quotient A V K hv ho,?_⟩
  have hFK' : F.subgroupOf N ≤ K := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hf hx
    exact (N.subtype_injective he) ▸ hk
  let v : (F.subgroupOf N).subgroupOf K ≃* F.subgroupOf N := subgroupOfEquivOfLe hFK'
  let q : F →* S := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp (QuotientGroup.mk' (pCore 2 F)))
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := q) hq
  let f : (F.subgroupOf N).subgroupOf K →* S :=
    q.comp (u.toMonoidHom.comp v.toMonoidHom)
  let : CommGroup (center K) := IsMulCommutative.instCommGroup
  let m : Group.SolvableKernelModel K (K ⧸ center K) := {
    kernel := center K
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := MulEquiv.refl _ }
  exact m.simple_section (Group.IsPerfect.not_isSolvable S) _ f
    (hq.comp (u.surjective.comp v.surjective))

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
