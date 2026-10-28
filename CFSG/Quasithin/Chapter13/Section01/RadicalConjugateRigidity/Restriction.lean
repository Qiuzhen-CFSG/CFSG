module

public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Overgroup

/-!
# Restriction of the original radical action to a local overgroup

The two characteristic quotients of X are unchanged when X is viewed
inside a containing subgroup. The explicit equivalence intertwines the
original conjugation action, allowing the rank-two comparison to be used
in a local group without replacing its irreducibility hypothesis.

Source: the passage to Mᵍ/O₂(Mᵍ) in Aschbacher--Smith 13.1.11, p.872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
open Chapter1
variable {G : Type*} [Group G]

private def restrictedQuotientEquiv {X M : Subgroup G} (hXM : X ≤ M) :
    XiQuotient (X.subgroupOf M) ≃* XiQuotient X :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXM)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXM))

private def restrictedFrattiniEquiv {X M : Subgroup G} (hXM : X ≤ M) :
    XiFrattiniQuotient (X.subgroupOf M) ≃* XiFrattiniQuotient X :=
  QuotientGroup.congr _ _ (restrictedQuotientEquiv hXM)
    (frattini_map_mulEquiv (restrictedQuotientEquiv hXM))

private theorem restrictedFrattiniEquiv_apply_mk {X M : Subgroup G}
    (hXM : X ≤ M) (x : X.subgroupOf M) :
    restrictedFrattiniEquiv hXM (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)) =
      QuotientGroup.mk' (frattini (XiQuotient X))
        (QuotientGroup.mk' (pCore 2 X) (subgroupOfEquivOfLe hXM x)) := rfl

private theorem restricted_equivariant {X S M : Subgroup G}
    (hXM : X ≤ M) (hn : S ≤ normalizer (X : Set G))
    (hn' : S.subgroupOf M ≤ normalizer (X.subgroupOf M : Set M))
    (s : S.subgroupOf M) (a : XiFrattiniQuotient (X.subgroupOf M)) :
    restrictedFrattiniEquiv hXM
      (xiFrattiniAction (S.subgroupOf M) (X.subgroupOf M) hn' s a) =
        xiFrattiniAction S X hn ⟨s, s.property⟩ (restrictedFrattiniEquiv hXM a) := by
  induction a using QuotientGroup.induction_on with | H a =>
    induction a using QuotientGroup.induction_on with | H x =>
      change restrictedFrattiniEquiv hXM
        (xiFrattiniAction (S.subgroupOf M) (X.subgroupOf M) hn' s
          (QuotientGroup.mk' _ (QuotientGroup.mk' _ x))) =
        xiFrattiniAction S X hn ⟨s, s.property⟩
          (restrictedFrattiniEquiv hXM (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
        restrictedFrattiniEquiv_apply_mk]
      rfl

/-- The containment result in a specified local subgroup, with the source
radical, acting group and iterated quotient retained literally. -/
theorem le_normal_radical_in [Finite G] {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (M X Y S : Subgroup G) (hM : IsStronglyQuasithin M)
    (hXM : X ≤ M) (hYM : Y ≤ M) (hSM : S ≤ M)
    (hYn : (Y.subgroupOf M).Normal)
    (hX : IsPPerfect 2 X) (hqX : XiOddQuotient p (XiQuotient X))
    (hqY : XiOddQuotient p (XiQuotient Y))
    (hXS : X ≤ S) (hn : S ≤ normalizer (X : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S X hn s a ∈ A) → A = ⊥ ∨ A = ⊤) :
    X ≤ Y := by
  let := hYn
  have hn' : S.subgroupOf M ≤ normalizer (X.subgroupOf M : Set M) :=
    (comap_mono hn).trans (X.le_normalizer_comap M.subtype)
  have hirr' : ∀ A : Subgroup (XiFrattiniQuotient (X.subgroupOf M)),
      (∀ s : S.subgroupOf M, ∀ a ∈ A,
        xiFrattiniAction (S.subgroupOf M) (X.subgroupOf M) hn' s a ∈ A) →
          A = ⊥ ∨ A = ⊤ := by
    intro A hA
    let e := restrictedFrattiniEquiv hXM
    have hi : ∀ s : S, ∀ a ∈ A.map e.toMonoidHom,
        xiFrattiniAction S X hn s a ∈ A.map e.toMonoidHom := by
      rintro s a ⟨b,hb,rfl⟩
      let s' : S.subgroupOf M := ⟨⟨s,hSM s.property⟩,s.property⟩
      refine ⟨xiFrattiniAction _ _ hn' s' b, hA s' b hb, ?_⟩
      exact restricted_equivariant hXM hn hn' s' b
    rcases hirr (A.map e.toMonoidHom) hi with hb | ht
    · exact Or.inl ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
    · right
      apply map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hle := le_normal_radical ho hM (X.subgroupOf M) (Y.subgroupOf M)
    (S.subgroupOf M)
    (hX.of_surjective (subgroupOfEquivOfLe hXM).symm.toMonoidHom
      (subgroupOfEquivOfLe hXM).symm.surjective)
    (hqX.of_mulEquiv (restrictedQuotientEquiv hXM).symm)
    (hqY.of_mulEquiv (restrictedQuotientEquiv hYM).symm)
    (subgroupOf_mono M hXS) hn' hirr'
  have hh := map_mono (f := M.subtype) hle
  simpa only [map_subgroupOf_eq_of_le hXM, map_subgroupOf_eq_of_le hYM] using hh

end CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
