module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Setup

/-!
# Quotient-rank obstructions to actor transfer

A rank-one E-member has actor image of rank exactly one in at least one of
its two defining quotients. In the component case, rank zero would make the
actor trivial and hence unable to move the nontrivial component. This gives
a test both for ambient generation and for the literal local actors.

These tests do not assert the proposed comparison between all intersections
`A ∩ JS` and actors `A ∈ Ω` contained in T. Intersections can have smaller
quotient rank. In particular, the chief-residual and local-normalizer
hypotheses alone do not justify that comparison; the missing source
component-generation bound must be retained in a revised assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.2 and E.1.5, printed p.210; application to the
actor-selection step of E.1.11, printed p.213.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

private theorem component_actor_rank_pos {T A K : Subgroup G}
    (h : ECaseComponent T A K) :
    0 < Group.rank ((A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))) := by
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  obtain ⟨_, _, _, L, hL, _, hact⟩ := h
  rcases hact with hact | hact
  · by_contra hn
    have hr : Group.rank a = 0 := Nat.eq_zero_of_not_pos hn
    have hs : Subsingleton a := Group.rank_eq_zero_iff.mp hr
    have ha : a = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact mem_bot.mpr (congrArg Subtype.val (@Subsingleton.elim a hs ⟨x, hx⟩ 1))
    change L = ⁅L, a⁆ at hact
    have hLb : L = ⊥ := by simpa only [ha, commutator_bot_right] using hact
    let _ := hL.2
    let _ : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    have hnt : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (nontrivial_iff_ne_bot L).mp hnt hLb
  · simpa only [hact.2] using Nat.zero_lt_one

/-- Rank zero is excluded in both branches of a rank-one E-member. -/
theorem rank_one_member_quotient_rank {T A K : Subgroup G}
    (h : IsEMemberAt 1 T A K) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 1 ∨
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) = 1 := by
  rcases h.2 with ⟨ho, _⟩ | ⟨hc, hr⟩
  · obtain ⟨p, _, _, _, _, _, hp⟩ := ho
    exact Or.inl hp
  · exact Or.inr (Nat.le_antisymm hr (component_actor_rank_pos hc))

/-- Excluding rank one in the two actual quotients excludes E-membership. -/
theorem not_rank_one_member_of_quotient_ranks (T A K : Subgroup G)
    (hcore : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1)
    (hrad : Group.rank ((A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))) ≠ 1) : ¬ IsEMemberAt 1 T A K := by
  intro h
  exact (rank_one_member_quotient_rank h).elim hcore hrad

/-- Apply the rank test to the literal local actor, with both intrinsic
quotients taken inside the proposed local member. -/
theorem local_actor_not_rank_one_member_of_quotient_ranks
    (T : Sylow 2 G) (J A : Subgroup G) (P : Subgroup (localGroup T J))
    (hcore : Group.rank (((A.subgroupOf (localGroup T J)).subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P))) ≠ 1)
    (hrad : Group.rank (((A.subgroupOf (localGroup T J)).subgroupOf P).map
      (QuotientGroup.mk' (solvableRadical P))) ≠ 1) :
    ¬ IsEMemberAt 1 ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P :=
  not_rank_one_member_of_quotient_ranks _ _ _ hcore hrad

/-- When the quotient ranks exclude all ambient E-members, the generation
target is exactly the weak-closure normalizer. Only candidates containing the
actor and its prescribed tau need to be tested. -/
theorem generationTarget_one_eq_normalizer_of_quotient_ranks
    (T : Sylow 2 G) (Ω : Set (Subgroup G))
    (hranks : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → ∀ K : Subgroup G,
      A ≤ K → tau (T : Subgroup G) A ≤ K →
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1 ∧
        Group.rank ((A.subgroupOf K).map
          (QuotientGroup.mk' (solvableRadical K))) ≠ 1) :
    generationTarget 1 T Ω = normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  have he : eFamilySubgroup 1 (T : Subgroup G) Ω = ⊥ := by
    apply eq_bot_iff.mpr
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    obtain ⟨hc, hr⟩ := hranks A.val A.property.1 A.property.2 K
      hK.1.2.2.1 (hK.1.2.2.2.1.trans inf_le_right)
    exact (not_rank_one_member_of_quotient_ranks _ _ _ hc hr hK).elim
  simp only [generationTarget, he, bot_sup_eq]

end CFSG.Quasithin.ChapterE.ChiefOrbit
