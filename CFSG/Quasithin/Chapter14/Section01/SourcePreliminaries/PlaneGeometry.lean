module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Source
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Ordering
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.CoreGrowth
public import Theory.GroupTheory.PCoreCommutator
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# The original plane branch: ordering and intersection core

The actual S₃ quotient makes the original Sylow act nontrivially on V.
Since |V|=4, its nonzero central seed has order two. The full14.1.12 source
then gives a unique ordering maximum. Every other local module lies between
this seed and V, so there are exactly two maximal locals, M and C_G(Z).

Reducedness identifies the core of the module centralizer with O₂(M).
Normal-core intersection gives C_R(V)=O₂(M), and original14.1.14 excludes
R=O₂(M). The normal centralizer also gives the required core commutator.
These are the original inputs to the literal residual splitting in14.1.18;
no old terminal certificate or additional core premise is used.
Source: Aschbacher--Smith14.1.17--18, printed pp.980--981.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03 Chapter15.Section03.InitialSource Chapter15.Section03.InitialSource.UniformControl
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

instance planeCentralizer_normal (T : Sylow 2 G) (M : Subgroup G) :
    ((centralizer (localModule T M : Set G)).subgroupOf M).Normal :=
  normal_subgroupOf_of_le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
    (normalizer_le_normalizer_centralizer _))

theorem plane_centralInvolutions_card (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3)) : Nat.card (centralInvolutions T) = 2 := by
  let V := localModule T M
  let Z := centralInvolutions T
  have hZV : Z ≤ V := le_conjugateSpanBy _ _
  have hZn : Z ≠ ⊥ := by
    intro hZ
    have hV : V = ⊥ := bot_unique (conjugateSpanBy_le hZ.le le_normalizer_of_normal)
    have hc : Nat.card V = 4 := hcard
    rw [hV,card_bot] at hc
    contradiction
  have hZne : Z ≠ V := by
    intro hZ
    let C := (centralizer (V : Set G)).subgroupOf M
    let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
    let S := (T.subtype hTM).mapSurjective hf
    have hn : (S : Subgroup (Equiv.Perm (Fin 3))) ≠ ⊥ := S.ne_bot_of_dvd_card
      (by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
    apply hn
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro t ht
    change e (QuotientGroup.mk t) = 1
    rw [←e.map_one,e.injective.eq_iff,QuotientGroup.eq_one_iff]
    intro z hz
    have hz' : z ∈ Z := by rw [hZ]; exact hz
    exact (centralInvolutions_le_centralizer_sylow T hz' t ht).symm
  have hd : Nat.card Z ∣ 2 ^ 2 := by
    have h := card_dvd_of_le hZV
    rw [show Nat.card V = 4 from hcard] at h
    exact h
  obtain ⟨k,hk,hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · exact (hZn (Z.eq_bot_of_card_eq hc)).elim
  · exact hc
  · exact (hZne (eq_of_le_of_card_ge hZV (by rw [hcard,hc]; decide))).elim

theorem plane_ordering_and_overgroups
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (hZ : Nat.card (centralInvolutions T) = 2) :
    (∀ N, IsOrderingMaximal T N → N = M) ∧ M ≠ Mc ∧
      Mc = centralizer (centralInvolutions T : Set G) ∧
      maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  obtain ⟨D,hD,Mf,hMf,hne,hmax,hBaum,hdom,hoff,hall,hC⟩ :=
    source_lemma_14_1_12_selection hG T hempty hu hmany
  have hMfM : M = Mf := hall hZ M hM
  subst Mf
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMcC.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hKM (K : Subgroup G) (hK : K ∈ maximalLocals T) :
      K = M ∨ K = centralizer (centralInvolutions T : Set G) := by
    have hVK : localModule T K ≤ localModule T M := (hdom K hK (Or.inr hZ)).span_le
    have hZK : centralInvolutions T ≤ localModule T K := le_conjugateSpanBy _ _
    have hd : Nat.card (localModule T K) ∣ 2 ^ 2 := by
      simpa only [hcard,show 2 ^ 2 = (4 : ℕ) from rfl] using card_dvd_of_le hVK
    have hlo : 2 ≤ Nat.card (localModule T K) := by
      simpa only [hZ] using Nat.card_le_card_of_injective _ (inclusion_injective hZK)
    obtain ⟨k,hk,hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k
    · have hh : Nat.card (localModule T K) = 1 := by simpa using hc
      omega
    · have he : centralInvolutions T = localModule T K :=
        eq_of_le_of_card_ge hZK (by rw [hZ,hc]; decide)
      right
      apply le_antisymm
      · rw [source_local_eq_normalizer hG T hK]
        change normalizer (localModule T K : Set G) ≤ _
        rw [←he]
        exact normalizer_le_centralizer_of_card_two _ hZ
      · have hn : IsTwoLocal (centralizer (centralInvolutions T : Set G)) := by
          have heq : normalizer (centralInvolutions T : Set G) =
              centralizer (centralInvolutions T : Set G) :=
            le_antisymm (normalizer_le_centralizer_of_card_two _ hZ) (Subgroup.centralizer_le_normalizer _)
          rw [←heq,he]
          rw [←source_local_eq_normalizer hG T hK]
          exact hK.1.1
        apply hK.1.2 hn
        rw [source_local_eq_normalizer hG T hK]
        change normalizer (localModule T K : Set G) ≤ _
        rw [←he]
        exact normalizer_le_centralizer_of_card_two _ hZ
    · left
      have he : localModule T K = localModule T M :=
        eq_of_le_of_card_ge hVK (by rw [hc,hcard]; decide)
      rw [source_local_eq_normalizer hG T hK,source_local_eq_normalizer hG T hM.1]
      exact congrArg (fun V : Subgroup G => normalizer (V : Set G)) he
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (hKM Mc ⟨hMcC.1,hTMc⟩).resolve_left (Ne.symm hne)
  refine ⟨hall hZ,hne,hMc,?_⟩
  ext K
  constructor
  · intro hK
    rcases hKM K hK with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (h.trans hMc.symm)))
  · intro hK
    rcases Set.mem_insert_iff.mp hK with rfl | hK
    · exact hM.1
    · rw [Set.mem_singleton_iff] at hK
      subst K
      exact ⟨hMcC.1,hTMc⟩

theorem plane_intersection_core_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : Nat.card (centralInvolutions T) = 2) (hne : M ≠ Mc) :
    (M ⊓ Mc).pCoreIn 2 ⊓ centralizer (localModule T M : Set G) = M.pCoreIn 2 ∧
      ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T M : Set G) ∧
      ⁅M ⊓ centralizer (localModule T M : Set G),(M ⊓ Mc).pCoreIn 2⁆ ≤ M.pCoreIn 2 := by
  let V := localModule T M
  let C := (centralizer (V : Set G)).subgroupOf M
  have hVM : V ≤ M := localModule_le T hM.2
  have hred := localModule_reduced_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  have hQK : pCore 2 M ≤ C := by
    have hi := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v,hVM hv⟩ hv)
  have hCI : C.map M.subtype ≤ M ⊓ Mc := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (localModule_centralizer_le_partner T M hu))
  have hCcore : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQK]
  have hQR : M.pCoreIn 2 ≤ (M ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) ((map_mono hQK).trans hCI)
      (inf_le_left.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have hQC : M.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (map_mono hQK).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  have hmeet : (M ⊓ Mc).pCoreIn 2 ⊓ centralizer (V : Set G) = M.pCoreIn 2 := by
    apply le_antisymm
    · have hi := inf_pCoreIn_le_of_le 2 hCI
      rw [←map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective,hCcore] at hi
      apply le_trans ?_ hi
      refine le_inf ?_ inf_le_left
      rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
      exact le_inf inf_le_right (inf_le_left.trans ((pCoreIn_le 2 _).trans inf_le_left))
    · exact le_inf hQR hQC
  refine ⟨hmeet,?_,?_⟩
  · intro hc
    have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := by
      intro t ht
      apply hMcC.2
      intro z hz
      exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
    apply intersection_core_ne_local_core hG T hempty hM ⟨hMcC.1,hTMc⟩ hu hmany hZ hne
    rwa [inf_eq_left.mpr hc] at hmeet
  · let H := (M ⊓ Mc).subgroupOf M
    have hCH : C ≤ H := by
      intro x hx
      exact hCI (mem_map_of_mem M.subtype hx)
    have he : H.pCoreIn 2 = ((M ⊓ Mc).pCoreIn 2).subgroupOf M := by
      apply map_injective M.subtype_injective
      rw [map_pCoreIn_of_injective 2 H M.subtype M.subtype_injective,
        show H.map M.subtype = M ⊓ Mc from map_subgroupOf_eq_of_le inf_le_left,
        map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)]
    have hh := map_mono (f := M.subtype) (commutator_pCoreIn_le_of_normal (p := 2) C H hCH)
    rw [map_commutator,he,map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left),
      show C.map M.subtype = M ⊓ centralizer (V : Set G) by
        rw [subgroupOf_map_subtype,inf_comm]] at hh
    exact hh

end CFSG.Quasithin.Chapter14.SourcePreliminaries
