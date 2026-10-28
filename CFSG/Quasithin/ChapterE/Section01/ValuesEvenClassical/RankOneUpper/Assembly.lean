module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupTheory.ConjugacyFamilySpan

/-!
# Assembly of the rank-one upper E-generation bounds

For a conjugation-invariant elementary family, the normalizer of its weak
closure contains the Sylow normalizer. Thus, when all proper Sylow overgroups
lie in one Borel, an E-member outside that Borel forces E-generation.
We also give the whole-group variant and a constructor that checks all of
E.1.2(E2) when the quotient has a single normal component. Its local tau orbit
is then that component, and the rank is measured after taking the radical
quotient, as required by E.1.5.

These are conditional assembly tools, not the PSL₂ or PSU₃ calculations.
The actual model and outer-automorphism calculations must supply their inputs.
In particular no bound on elementary ranks in a unitary extension is assumed
here. The PSU₃ model uses the matrix field of order 2^(2f).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--E.1.6 and E.1.14(1), printed pp.209--211, 214. E.1.14 cites
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The Borel contribution to generation is available for every invariant
family, even when the family has no members in the chosen Sylow subgroup. -/
theorem normalizer_le_weakClosure_normalizer (T : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    normalizer (T : Set G) ≤ normalizer (weakClosure T Ω : Set G) :=
  SubgroupFamily.normalizer_le_span_normalizer (fun A hA g => hΩ.2 g A hA) T

omit [Finite G] in
/-- An empty nontrivial part of the family has trivial weak closure. -/
theorem weakClosure_eq_bot_of_members_eq_bot (T : Subgroup G)
    (Ω : Set (Subgroup G))
    (h : ∀ A ∈ Ω, A ≤ T → A = ⊥) : weakClosure T Ω = ⊥ := by
  apply le_bot_iff.mp
  exact sSup_le fun A hA => (h A hA.1 hA.2).le

/-- A top E-member settles every family containing a nontrivial member in T;
the remaining families have full weak-closure normalizer. -/
theorem isEGeneratedAt_of_top_members {i : ℕ} (T : Sylow 2 G)
    (htop : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → IsEMemberAt i (T : Subgroup G) A ⊤) :
    IsEGeneratedAt i T := by
  classical
  intro Ω hΩ
  by_cases hex : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧ A ≠ ⊥
  · obtain ⟨A, hA, hAT, hne⟩ := hex
    apply top_unique
    exact (show (⊤ : Subgroup G) ≤ eSubgroup i (T : Subgroup G) A from
      le_sSup (htop A (hΩ.1 A hA) hAT hne)).trans
      ((le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)} =>
        eSubgroup i (T : Subgroup G) B.1) ⟨A, hA, hAT⟩).trans le_sup_left)
  · have hW : weakClosure (T : Subgroup G) Ω = ⊥ :=
      weakClosure_eq_bot_of_members_eq_bot _ _ (fun A hA hAT => by
        by_contra hne
        exact hex ⟨A, hA, hAT, hne⟩)
    rw [hW, normalizer_eq_top, sup_top_eq]

/-- In rank one, the local calculation only needs to produce an E-member
outside the unique proper Sylow overgroup when the weak-closure normalizer
has not already escaped it. -/
theorem isEGeneratedAt_of_borel_escape {i : ℕ} (T : Sylow 2 G)
    (B : Subgroup G)
    (hB : ∀ M : Subgroup G, (T : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B)
    (hescape : ∀ Ω : Set (Subgroup G), IsElementaryFamily Ω →
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ B →
      ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
        ∃ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K ∧ ¬ K ≤ B) :
    IsEGeneratedAt i T := by
  intro Ω hΩ
  by_contra hproper
  have hTB : (T : Subgroup G) ≤
      eFamilySubgroup i (T : Subgroup G) Ω ⊔
        normalizer (weakClosure (T : Subgroup G) Ω : Set G) :=
    (Subgroup.le_normalizer.trans
      (normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans le_sup_right
  have hgenB := hB _ hTB hproper
  obtain ⟨A, hA, hAT, K, hK, hKB⟩ := hescape Ω hΩ (le_sup_right.trans hgenB)
  apply hKB
  exact (show K ≤ eSubgroup i (T : Subgroup G) A from le_sSup hK).trans
    ((le_iSup (fun C : {C : Subgroup G // C ∈ Ω ∧ C ≤ (T : Subgroup G)} =>
      eSubgroup i (T : Subgroup G) C.1) ⟨A, hA, hAT⟩).trans
        (le_sup_left.trans hgenB))

/-- Quotient images of A inside an overgroup have no larger generator rank.
This compares actual groups, including the intrinsic `subgroupOf` carrier. -/
theorem rank_quotient_image_le (A K : Subgroup G) (hAK : A ≤ K)
    (N : Subgroup K) [N.Normal] :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ Group.rank A := by
  calc
    _ ≤ Group.rank (A.subgroupOf K) :=
      Group.rank_le_of_surjective ((QuotientGroup.mk' N).subgroupMap _)
        ((QuotientGroup.mk' N).subgroupMap_surjective _)
    _ = Group.rank A := Group.rank_congr (subgroupOfEquivOfLe hAK)

/-- The local tau orbit of a normal component is that component. -/
theorem conjugateJoin_eq_of_normal {H : Type*} [Group H]
    (D C : Subgroup H) [C.Normal] : conjugateJoin D C = C := by
  simp [conjugateJoin, Subgroup.Normal.map_conj_eq]

/-- A constructor for the single-normal-component case. In particular the
2-residual is not confused with the 2-core, and Sylow-ness is intrinsic to K.
The normal component and every structural condition must be proved by the
local model calculation. -/
theorem isEMemberAt_of_normal_quotient_component {i : ℕ}
    (T A K : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ T) (hAK : A ≤ K)
    (htau : tau T A ≤ K)
    (hSyl : ∃ S : Sylow 2 K, (S : Subgroup K) = T.subgroupOf K)
    (hclosed : IsTwoClosed (solvableRadical K))
    (hquot : HasTwoGroupQuotient (componentLayer (K ⧸ solvableRadical K)))
    (hres : pResidual 2 K = solvableResidual K)
    (C : Subgroup (K ⧸ solvableRadical K)) [C.Normal]
    (hC : IsComponent (K ⧸ solvableRadical K) C)
    (hlayer : componentLayer (K ⧸ solvableRadical K) = C)
    (hcomm : C = ⁅C, (A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))⁆)
    (hrank : Group.rank ((A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))) ≤ i) :
    IsEMemberAt i T A K := by
  have hc : ECaseComponent T A K := by
    refine ⟨hclosed, hquot, hres, C, hC, ?_, Or.inl hcomm⟩
    rw [conjugateJoin_eq_of_normal, hlayer]
  exact ⟨⟨hA, hAT, hAK, le_inf (tau_le T A) htau, hSyl, Or.inr hc⟩,
    Or.inr ⟨hc, hrank⟩⟩

/-- The whole group is an E-member once its component case and the elementary
rank bound have been checked. -/
theorem isEMemberAt_top_of_component_and_rank {i : ℕ} (T : Sylow 2 G)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup G))
    (hc : ECaseComponent (T : Subgroup G) A ⊤) (hrank : Group.rank A ≤ i) :
    IsEMemberAt i (T : Subgroup G) A ⊤ := by
  exact ⟨⟨hA, hAT, le_top, le_inf (tau_le _ _) le_top,
    ⟨T.subtype le_top, rfl⟩, Or.inr hc⟩,
    Or.inr ⟨hc, (rank_quotient_image_le A ⊤ le_top _).trans hrank⟩⟩

/-- For PSL₂-type rank bounds, the original elementary rank bound suffices;
the E2 structure itself remains a separate, explicit input. -/
theorem isEGeneratedAt_of_top_component_and_rank {i : ℕ} (T : Sylow 2 G)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → Group.rank A ≤ i) :
    IsEGeneratedAt i T := by
  apply isEGeneratedAt_of_top_members T
  intro A hA hAT hne
  exact isEMemberAt_top_of_component_and_rank T A hA hAT
    (hcomponent A hA hAT hne) (hrank A hA hAT)

/-- The unitary route separates families having a small nontrivial member
from those whose nontrivial members all exceed the desired rank. Only the
latter families require a proper local subgroup outside the Borel. -/
theorem isEGeneratedAt_of_small_top_members_or_escape {i : ℕ} (T : Sylow 2 G)
    (B : Subgroup G) (hBproper : B ≠ ⊤)
    (hB : ∀ M : Subgroup G, (T : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hlarge : ∀ Ω : Set (Subgroup G), IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → i < Group.rank A) →
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ B →
      ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
        ∃ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K ∧ ¬ K ≤ B) :
    IsEGeneratedAt i T := by
  classical
  apply isEGeneratedAt_of_borel_escape T B hB
  intro Ω hΩ hnorm
  by_cases hsmall : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
      A ≠ ⊥ ∧ Group.rank A ≤ i
  · obtain ⟨A, hA, hAT, hne, hrank⟩ := hsmall
    exact ⟨A, hA, hAT, ⊤,
      isEMemberAt_top_of_component_and_rank T A (hΩ.1 A hA) hAT
        (hcomponent A (hΩ.1 A hA) hAT hne) hrank,
      fun h => hBproper (top_unique h)⟩
  · apply hlarge Ω hΩ _ hnorm
    intro A hA hAT hne
    exact Nat.lt_of_not_ge (fun h => hsmall ⟨A, hA, hAT, hne, h⟩)

/-- A pointwise local construction for elementary subgroups of excessive
rank suffices for the unitary branch. A proper weak-closure normalizer ensures
that the family contains a nontrivial member to which it can be applied. -/
theorem isEGeneratedAt_of_rank_dichotomy {i : ℕ} (T : Sylow 2 G)
    (B : Subgroup G) (hBproper : B ≠ ⊤)
    (hB : ∀ M : Subgroup G, (T : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hlarge : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → i < Group.rank A →
      ∃ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K ∧ ¬ K ≤ B) :
    IsEGeneratedAt i T := by
  classical
  apply isEGeneratedAt_of_small_top_members_or_escape T B hBproper hB hcomponent
  intro Ω hΩ hrank hnorm
  have hex : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧ A ≠ ⊥ := by
    by_contra h
    have hW : weakClosure (T : Subgroup G) Ω = ⊥ :=
      weakClosure_eq_bot_of_members_eq_bot _ _ (fun A hA hAT => by
        by_contra hne
        exact h ⟨A, hA, hAT, hne⟩)
    rw [hW, normalizer_eq_top] at hnorm
    exact hBproper (top_unique hnorm)
  obtain ⟨A, hA, hAT, hne⟩ := hex
  obtain ⟨K, hK, hKB⟩ := hlarge A (hΩ.1 A hA) hAT (hrank A hA hAT hne)
  exact ⟨A, hA, hAT, K, hK, hKB⟩

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
