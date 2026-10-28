module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Original local inputs for the cubic rigidity rows

The plane source provides the containing centralizer, its characteristic-two
property, the actual intersection with M, and uniqueness above YT. Uniqueness
controls normalizers of nontrivial two-subgroups normalized by YT. The original
four-plane is the conjugate span of the same central involution under YT.
These inputs retain the original groups for the four model applications.
Source: Aschbacher–Smith, 14.2.21, printed p.988.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original local context shared by the four cubic rigidity rows. -/
structure CubicSourceContext (T : Sylow 2 G) (M Mc H : Subgroup G) : Prop where
  sylow_le_H : (T : Subgroup G) ≤ H
  H_le_Mc : H ≤ Mc
  Mc_centralizer : Mc = centralizer (centralInvolutions T : Set G)
  mark_card : Nat.card (centralInvolutions T) = 2
  H_inf_M : H ⊓ M = (T : Subgroup G)
  Mc_characteristic_two : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc
  module_card : Nat.card (localModule T M) = 4
  module_normalizer : M = normalizer (localModule T M : Set G)
  module_span : localModule T M = localSpan (centralInvolutions T)
    (sourceResidual M Mc ⊔ (T : Subgroup G))
  normalizer_control : ∀ E : Subgroup G, IsPGroup 2 E → E ≠ ⊥ →
    sourceResidual M Mc ⊔ (T : Subgroup G) ≤ normalizer (E : Set G) →
    normalizer (E : Set G) ≤ M
  decomposition : M ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔
    (M ⊓ centralizer (localModule T M : Set G))

/-- All shared local hypotheses follow from the original plane source. -/
theorem cubic_source_context
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) : CubicSourceContext T M Mc H := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc : H ≤ Mc := hMc ▸
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTMc : (T : Subgroup G) ≤ Mc := hTH.trans hHMc
  have hMcMem : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hMcMem.1.1,hTMc⟩)
  have hint : H ⊓ M = (T : Subgroup G) := by
    have hh := (sylow_normalizer_small_core_quotient (T.subtype hTH)
      (SmallSolvableModel.card (Or.inr (Or.inr ⟨eH⟩)))).2
      (M.subgroupOf H) (fun x hx => hM.1.2 hx) (lt_top_iff_ne_top.mpr (by
        intro ht
        apply hH.1.2
        intro x hx
        exact show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from ht.ge (mem_top _)))
    have hm := congrArg (Subgroup.map H.subtype) hh
    rw [subgroupOf_map_subtype,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,inf_comm] at hm
    exact hm
  obtain ⟨_,_,_,_,_,_,huniq,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hcontrol (E : Subgroup G) (hp : IsPGroup 2 E) (hn : E ≠ ⊥)
      (hXE : X ≤ normalizer (E : Set G)) : normalizer (E : Set G) ≤ M := by
    apply normalizer_le_of_unique_maximalTwoLocal _ hp hn hXE
    intro N hN hXN
    have hm : N ∈ maximalTwoLocalOvergroups X := ⟨hN,hXN⟩
    exact Set.mem_singleton_iff.mp (huniq ▸ hm)
  have hW : localSpan (centralInvolutions T) X ≤ localModule T M :=
    conjugateSpanBy_mono le_rfl hXM
  have hZW : centralInvolutions T ≤ localSpan (centralInvolutions T) X :=
    le_conjugateSpanBy _ _
  have hZne : centralInvolutions T ≠ localSpan (centralInvolutions T) X := by
    intro he
    have hXZ : X ≤ normalizer (centralInvolutions T : Set G) :=
      he.symm ▸ le_normalizer_conjugateSpanBy (centralInvolutions T) X
    have hXMc : X ≤ Mc := hMc.symm ▸
      hXZ.trans (normalizer_le_centralizer_of_card_two _ hZ)
    have hm : Mc ∈ maximalTwoLocalOvergroups X := ⟨hMcMem.1,hXMc⟩
    exact hne (Set.mem_singleton_iff.mp (huniq ▸ hm)).symm
  have hspan : localModule T M = localSpan (centralInvolutions T) X := by
    have hd : Nat.card (localSpan (centralInvolutions T) X) ∣ 2 ^ 2 := by
      simpa only [hcard,show 2 ^ 2 = (4 : ℕ) from rfl] using card_dvd_of_le hW
    have hlo : 2 ≤ Nat.card (localSpan (centralInvolutions T) X) := by
      simpa only [hZ] using Nat.card_le_card_of_injective _ (inclusion_injective hZW)
    obtain ⟨k,hk,hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k
    · have hc' : Nat.card (localSpan (centralInvolutions T) X) = 1 := by simpa using hc
      omega
    · exact (hZne (eq_of_le_of_card_ge hZW (by rw [hZ,hc]; decide))).elim
    · exact (eq_of_le_of_card_ge hW (by rw [hc,hcard]; decide)).symm
  obtain ⟨_,hnoncentral,_⟩ :=
    plane_intersection_core_inputs hG T hempty hM.1 hu hmany hZ hne
  exact ⟨hTH,hHMc,hMc,hZ,hint,hc,hcard,
    InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1,hspan,hcontrol,
    (decomposition_of_intersectionCore_not_centralizing M Mc (localModule T M) T
      hM.1.2 ⟨e⟩ hnoncentral).le⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
