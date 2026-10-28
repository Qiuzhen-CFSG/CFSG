module
public import CFSG.Quasithin.Chapter14.Section02.ProperComponent
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Ordering
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The residual span and the noncentral component

The normal residual Y together with T has unique maximal local M. Its
orbit on the original central line therefore spans the four-plane V;
normality of Y removes T from this span. A component normalized by Y that
centralized the line would then centralize V and lie in M, contradicting
the original outside overgroup. Uniqueness above that overgroup also rules
out the component normalizing any nontrivial characteristic subgroup of S.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_plane_module_residual_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    localModule T M = conjugateSpanBy (centralInvolutions T) (sourceResidual M Mc) := by
  let Y := sourceResidual M Mc
  let X := Y ⊔ (T : Subgroup G)
  have hYM : Y ≤ M := sourceResidual_le _ _
  have hXM : X ≤ M := sup_le hYM hM.1.2
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  obtain ⟨_,_,_,_,_,_,huniq,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hW : conjugateSpanBy (centralInvolutions T) X ≤ localModule T M :=
    conjugateSpanBy_mono le_rfl hXM
  have hZW : centralInvolutions T ≤ conjugateSpanBy (centralInvolutions T) X :=
    le_conjugateSpanBy _ _
  have hZne : centralInvolutions T ≠ conjugateSpanBy (centralInvolutions T) X := by
    intro he
    have hXZ : X ≤ normalizer (centralInvolutions T : Set G) :=
      he.symm ▸ le_normalizer_conjugateSpanBy (centralInvolutions T) X
    have hXMc : X ≤ Mc := hMc.symm ▸
      hXZ.trans (normalizer_le_centralizer_of_card_two _ hZ)
    have hm : Mc ∈ maximalTwoLocalOvergroups X := by
      refine ⟨?_,hXMc⟩
      exact (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G))
        from hu ▸ Set.mem_singleton Mc).1
    exact hne (Set.mem_singleton_iff.mp (huniq ▸ hm)).symm
  have hspan : localModule T M = conjugateSpanBy (centralInvolutions T) X := by
    have hd : Nat.card (conjugateSpanBy (centralInvolutions T) X) ∣ 2 ^ 2 := by
      simpa only [hcard,show 2 ^ 2 = (4 : ℕ) from rfl] using card_dvd_of_le hW
    have hlo : 2 ≤ Nat.card (conjugateSpanBy (centralInvolutions T) X) := by
      simpa only [hZ] using Nat.card_le_card_of_injective _ (inclusion_injective hZW)
    obtain ⟨k,hk,hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k
    · have hc' : Nat.card (conjugateSpanBy (centralInvolutions T) X) = 1 := by simpa using hc
      omega
    · exact (hZne (eq_of_le_of_card_ge hZW (by rw [hZ,hc]; decide))).elim
    · exact (eq_of_le_of_card_ge hW (by rw [hc,hcard]; decide)).symm
  rw [hspan]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
      (_root_.centralizer_le_normalizer _))
    (hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc)))

theorem source_proper_completion_component_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ¬ L ≤ centralizer (centralInvolutions T : Set G) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ¬ L ≤ centralizer (centralInvolutions T : Set G)
  obtain ⟨_,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hs
  have hLX : L ≤ X := map_subtype_le _
  have hLN : X ≤ normalizer (L : Set G) := by
    have hh := (solvableResidual X).le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  intro hLZ
  have hLV : L ≤ centralizer (localModule T M : Set G) := by
    rw [source_plane_module_residual_span hG T hempty hM hu hmany hcard e]
    exact le_centralizer_conjugateSpanBy_of_normalizes _ _ _
      ((le_sup_right.trans le_sup_left : sourceResidual M Mc ≤ X).trans hLN) hLZ
  have hLM : L ≤ M := by
    rw [InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    exact hLV.trans (_root_.centralizer_le_normalizer _)
  apply hH.1.2
  rw [←hgen]
  exact sup_le (hKL.trans hLM) hM.1.2
theorem source_proper_component_characteristic_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S L : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hgen : K ⊔ (T : Subgroup G) = H) (hKL : K ≤ L)
    (hLZ : ¬ L ≤ centralizer (centralInvolutions T : Set G)) :
    ∀ C : Subgroup S, C.Characteristic → C ≠ ⊥ →
      ¬ L ≤ normalizer (C.map S.subtype : Set G) := by
  intro C hC hne hLN
  let := hC
  have hNT : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hi)
  have hTN : (T : Subgroup G) ≤ normalizer (C.map S.subtype : Set G) :=
    hNT.trans (normalizer_le_normalizer_characteristic_image S C)
  have hN : normalizer (C.map S.subtype : Set G) ≤ Mc := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := H)
    · intro N hN hHN
      have huniq := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
        H hH.1.1 hH.1.2).1
      exact Set.mem_singleton_iff.mp (huniq ▸ ⟨hN,hHN⟩)
    · exact ((T.isPGroup'.to_le hST).to_subgroup C).map S.subtype
    · intro he
      exact hne ((C.map_eq_bot_iff_of_injective S.subtype_injective).mp he)
    · rw [←hgen]
      exact sup_le (hKL.trans hLN) hTN
  have he := (plane_ordering_and_overgroups hG T hempty hM hu hmany hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e)).2.2.1
  exact hLZ ((hLN.trans hN).trans he.le)

end CFSG.Quasithin.Chapter14.Section02
