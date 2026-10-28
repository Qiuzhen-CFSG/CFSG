module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Ordering
/-!
# The original normalizer choice and the Mf conclusions of14.1.12

Choose an actual maximal two-local Mf above the normalizer of the fixed
nontrivial characteristic subgroup C₂ of Baum(T). The precise preceding
14.1.11 factorizations give all source ordering comparisons. Their central
factors lie in Mc, so Mf cannot equal Mc. Finite-order maximality and the
actual module normalizers then make Mf the unique maximum outside Mc,
and the unique maximum everywhere when the central omega group has order2.
The same comparisons place C_Mf(V(Mf)) in every original maximal local.

A second Frattini argument, for the actual intersection C_T(Vf), gives
Mf as its relative normalizer's unique maximal two-local overgroup for
any normal Vf containing V(Mf). This is the literal14.1.12(2) application
of A.5.7, with no assumed normalizer-uniqueness certificate.

The first theorem retains exactly the prior14.1.11 factorization on ONE
fixed C₂. Its noncentral fixed-pair C.1.28 source is an independent producer;
this module does not assert that source premise or full Theorem E.
Source: Aschbacher–Smith14.1.11–12, printed pp.978–979.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterA.Section05To06 ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem ordering_of_centralizer_supplement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M P : Subgroup G} (hM : M ∈ maximalLocals T)
    (A : Subgroup G) (hAM : A ≤ M)
    (hfac : M = (M ⊓ centralizer (localModule T M : Set G)) ⊔ A)
    (hAP : A ≤ P) :
    OrderingLE T M P := by
  let V := localModule T M
  let N := M ⊓ centralizer (V : Set G)
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let := (localModule_reduced_from_source hG T hH).normal
  have hVM : V ≤ M := conjugateSpanBy_le_self
    (fun z hz => hM.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hN : N.subgroupOf M = centralizer (V.subgroupOf M : Set M) := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show N ≤ M from inf_le_left),map_centralizer_subtype,
      map_subgroupOf_eq_of_le hVM]
  let : (N.subgroupOf M).Normal := hN ▸ inferInstance
  have hgen : A.subgroupOf M ⊔ N.subgroupOf M = ⊤ := by
    rw [←subgroupOf_sup hAM (show N ≤ M from inf_le_left),sup_comm]
    rw [←hfac,subgroupOf_self]
  intro m hm
  have hmem : (⟨m,hm⟩ : M) ∈ A.subgroupOf M ⊔ N.subgroupOf M := by
    rw [hgen]; exact mem_top _
  obtain ⟨a,ha,c,hc,he⟩ := mem_sup_of_normal_right.mp hmem
  exact ⟨a,⟨a.property,hAP ha⟩,c,hc,congrArg M.subtype he⟩

omit [Finite G] in
private theorem eq_partner_of_ordering
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalLocals T)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hord : OrderingLE T M Mc) : M = Mc := by
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  apply hM.1.eq_of_le hMc.1
  intro m hm
  obtain ⟨a,ha,c,hc,rfl⟩ := hord m hm
  exact Mc.mul_mem ha.2 (centralizer_le_partner T hu
    (centralizer_le (le_conjugateSpanBy (centralOmega T) M) hc.2))

/-- The original normalizer choice in14.1.12, consuming exactly the
preceding14.1.11 factorization for this ONE characteristic subgroup. -/
theorem source_normalizer_selection_of_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G) {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (C : Subgroup (baumann (T : Subgroup G))) [C.Characteristic] (hne : C ≠ ⊥)
    (hfac : ∀ M ∈ maximalLocals T, M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2 →
      M = (M ⊓ centralizer (localModule T M : Set G)) ⊔
        (M ⊓ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G))) :
    ∃ Mf : Subgroup G,
      Mf ∈ maximalTwoLocalOvergroups
        (normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      Mf ≠ Mc ∧ IsOrderingMaximal T Mf ∧
      (∀ M ∈ maximalLocals T, M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2 → OrderingLE T M Mf) ∧
      (∀ M ∈ maximalLocals T, M ≠ Mc →
        (∀ N ∈ maximalLocals T, N ≠ Mc → OrderingLE T M N → N = M) → M = Mf) ∧
      (Nat.card (centralInvolutions T) = 2 → ∀ M, IsOrderingMaximal T M → M = Mf) ∧
      (∀ M ∈ maximalLocals T,
        Mf ⊓ centralizer (localModule T Mf : Set G) ≤ M) := by
  let B := baumann (T : Subgroup G)
  let D := C.map B.subtype
  have hDne : D ≠ ⊥ := fun hd => hne ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp hd)
  have hp : IsPGroup 2 D := ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).to_subgroup C).map B.subtype
  have hloc : IsTwoLocal (normalizer (D : Set G)) := ⟨D,hDne,hp,rfl⟩
  obtain ⟨Mf,hNMf,hMf⟩ := Finite.exists_le_maximal hloc
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ C)
  have hMfT : Mf ∈ maximalLocals T := ⟨hMf,hTN.trans hNMf⟩
  have hord (M : Subgroup G) (hM : M ∈ maximalLocals T)
      (he : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2) : OrderingLE T M Mf :=
    ordering_of_centralizer_supplement hG T hM _ inf_le_left (hfac M hM he) (inf_le_right.trans hNMf)
  have hneq : Mf ≠ Mc := by
    intro he
    have hall (M : Subgroup G) (hM : M ∈ maximalLocals T) : M = Mc := by
      by_cases hm : M = Mc
      · exact hm
      · exact eq_partner_of_ordering T hM hu (he ▸ hord M hM (Or.inl hm))
    obtain ⟨M,hM,N,hN,hMN⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    exact hMN ((hall M hM).trans (hall N hN).symm)
  have hmax : IsOrderingMaximal T Mf := by
    refine ⟨hMfT,?_⟩
    intro N hN hMN
    have hneN : N ≠ Mc := by
      intro he
      exact hneq (eq_partner_of_ordering T hMfT hu (he ▸ hMN))
    exact conjugateSpanLE_antisymm (source_local_eq_normalizer hG T hN)
      (source_local_eq_normalizer hG T hMfT) (hord N hN (Or.inl hneN)) hMN
  refine ⟨Mf,⟨hMf,hNMf⟩,hneq,hmax,hord,?_,?_,?_⟩
  · intro M hM hneM hmaxM
    exact (hmaxM Mf hMfT hneq (hord M hM (Or.inl hneM))).symm
  · intro hz M hM
    exact (hM.2 Mf hMfT (hord M hM.1 (Or.inr hz))).symm
  · intro M hM
    by_cases he : M = Mc
    · rw [he]
      exact inf_le_right.trans ((centralizer_le (le_conjugateSpanBy (centralOmega T) Mf)).trans
        (centralizer_le_partner T hu))
    · have hnormal : M ∈ normalizerOvergroups T :=
        ⟨⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩,source_local_eq_normalizer hG T hM⟩
      exact ((lemma_A_5_3 (hord M hM (Or.inl he))).2.2 hnormal).trans inf_le_left

private theorem relative_sylow_frattini (T : Sylow 2 G) (M N : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hNM : N ≤ M) [(N.subgroupOf M).Normal] :
    M = N ⊔ (M ⊓ normalizer ((T : Subgroup G) ⊓ N : Subgroup G)) := by
  let S := T.subtype hTM
  let K := N.subgroupOf M
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPK : ((P : Subgroup K).map K.subtype).map M.subtype =
      (T : Subgroup G) ⊓ N := by
    rw [hP,subgroupOf_map_subtype,Subgroup.map_inf _ _ M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,map_subgroupOf_eq_of_le hNM]
  have hn : (normalizer ((P : Subgroup K).map K.subtype : Set M)).map M.subtype ≤
      normalizer ((T : Subgroup G) ⊓ N : Subgroup G) := by
    have h := ((P : Subgroup K).map K.subtype).le_normalizer_map M.subtype
    rwa [hPK] at h
  have hf := congrArg (map M.subtype) P.normalizer_sup_eq_top
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hNM] at hf
  apply le_antisymm
  · exact hf.symm.le.trans (sup_le (le_sup_of_le_right (le_inf (map_subtype_le _) hn)) le_sup_left)
  · exact sup_le hNM inf_le_left

/-- The genuine Frattini application in14.1.12(2), for every actual normal
Vf containing the canonical module of the selected ordering maximum. -/
theorem source_unique_overgroup_sylow_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (Vf : Subgroup G) (hVV : localModule T M ≤ Vf) (hVM : Vf ≤ M)
    [(Vf.subgroupOf M).Normal] :
    maximalTwoLocalOvergroups
      (M ⊓ normalizer ((T : Subgroup G) ⊓ centralizer (Vf : Set G) : Subgroup G)) = {M} := by
  let N := M ⊓ centralizer (Vf : Set G)
  let X := M ⊓ normalizer ((T : Subgroup G) ⊓ centralizer (Vf : Set G) : Subgroup G)
  have hN : N.subgroupOf M = centralizer (Vf.subgroupOf M : Set M) := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show N ≤ M from inf_le_left),map_centralizer_subtype,
      map_subgroupOf_eq_of_le hVM]
  let : (N.subgroupOf M).Normal := hN ▸ inferInstance
  have hTI : (T : Subgroup G) ⊓ N = (T : Subgroup G) ⊓ centralizer (Vf : Set G) := by
    change (T : Subgroup G) ⊓ (M ⊓ centralizer (Vf : Set G)) = _
    rw [←inf_assoc,inf_eq_left.mpr hM.1.2]
  have hfac : M = N ⊔ X := by
    simpa only [hTI] using relative_sylow_frattini T M N hM.1.2 inf_le_left
  have hNV : N ≤ M ⊓ centralizer (localModule T M : Set G) :=
    inf_le_inf_left _ (centralizer_le hVV)
  have hfull : M = (M ⊓ centralizer (localModule T M : Set G)) ⊔ X := by
    apply le_antisymm (hfac.le.trans (sup_le_sup_right hNV X))
    exact sup_le inf_le_left inf_le_left
  have hTX : (T : Subgroup G) ≤ X := by
    refine le_inf hM.1.2 ?_
    apply le_trans _ (inf_normalizer_le_normalizer_inf)
    refine le_inf (T : Subgroup G).le_normalizer ?_
    exact ((hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer hVM).mp inferInstance)).trans
      (normalizer_le_normalizer_centralizer Vf))
  have horder : OrderingLE T M X :=
    ordering_of_centralizer_supplement hG T hM.1 X inf_le_left hfull le_rfl
  have hu := lemma_A_5_7_1 hM hTX (show X ≤ M from inf_le_left) horder
  ext K
  constructor
  · intro hK
    exact Set.mem_singleton_iff.mpr ((hu K hK.1).mp hK.2)
  · rintro rfl
    exact ⟨hM.1.1,inf_le_left⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
