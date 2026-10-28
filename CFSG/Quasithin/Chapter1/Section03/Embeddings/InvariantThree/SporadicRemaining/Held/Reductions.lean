module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.LocalPairs.Transport

/-!
# Reductions for the retained Held branch

The exact source PairInput is unchanged. A local overgroup whose order is
not divisible by 27 excludes the extraspecial complement and identifies the
remaining complement with the actual elementary plane. Constructing such
overgroups uniformly is still a separate coverage obligation.

The full permutation-normalizer action has image exactly pairAutomizer when
the full automorphism realization is supplied. Transport to a chosen plane
equivalence retains that exact image, including outer actors. No dihedral
exhaustiveness or universal reducibility is asserted.

Sources: Aschbacher–Smith, printed p.511 and Theorem C on p.33; GLS3,
Table 5.3p. The uniform Held branch and its local normalizer calculations
remain open until their coverage and realization premises are discharged.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

/-- Restrict only the inner automorphisms preserving the pair. This action is
kept separate from the full extending action throughout. -/
def innerPairAction (S R : Subgroup Held.He) :
    actingPairStabilizer (MulAut.conj : Held.He →* MulAut Held.He) S R →* MulAut R :=
  actingPairRestriction (MulAut.conj : Held.He →* MulAut Held.He) S R

/-- The abstract restriction construction gives the entire source automizer. -/
theorem pairRestriction_range (S R : Subgroup Held.He) :
    (pairRestriction S R).range = pairAutomizer S R := by
  ext a
  exact mem_pairRestriction_range_iff S R a

/-- The inherited quasisimplicity becomes simplicity using concrete centerlessness.
This supplies the existing realization task's permitted simplicity hypothesis. -/
theorem simple_of_pairInput {S : Sylow 2 Held.He} {R : Subgroup Held.He}
    (h : PairInput S R) : IsSimpleGroup Held.He := by
  let e : Held.He ⧸ center Held.He ≃* Held.He :=
    (QuotientGroup.quotientMulEquivOfEq Held.LocalPairs.center_eq_bot).trans
      QuotientGroup.quotientBot
  exact e.isSimpleGroup_congr.mp h.quasisimple.simple

/-- The uniform pair task can obtain E₉ from a verified local overgroup.
The overgroup need not be unique or maximal. -/
theorem plane_of_overgroup {S : Sylow 2 Held.He} {R : Subgroup Held.He}
    (h : PairInput S R) (K : Subgroup Held.He) (hRK : R ≤ K)
    (hK : ¬ 27 ∣ Nat.card K) : Nonempty (R ≃* Plane 3) := by
  apply plane_of_odd_complement_card h.oddComplement
  intro hcard
  apply hK
  have hd := Subgroup.card_dvd_of_le hRK
  norm_num only [hcard, Nat.reducePow] at hd
  exact hd

/-- Full automorphism realization identifies the entire extending action. -/
theorem permutationPairAction_range
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) :
    (Held.LocalPairs.permutationPairAction S R).range = pairAutomizer S R := by
  change (actingPairRestriction Held.permutationGroup.normalizerMonoidHom S R).range = _
  rw [actingPairRestriction_range _ hrealize]
  ext a
  exact mem_pairRestriction_range_iff S R a

/-- Plane coordinates for the action, using an actual group equivalence. -/
def planeAction (S R : Subgroup Held.He) (e : R ≃* Plane 3) :
    Held.LocalPairs.permutationPairStabilizer S R →* MulAut (Plane 3) :=
  (MulAut.congr e).toMonoidHom.comp (Held.LocalPairs.permutationPairAction S R)

/-- The coordinate action is intertwined with the original action on R. -/
theorem planeAction_apply (S R : Subgroup Held.He) (e : R ≃* Plane 3)
    (a : Held.LocalPairs.permutationPairStabilizer S R) (x : R) :
    planeAction S R e a (e x) = e (Held.LocalPairs.permutationPairAction S R a x) := by
  change e (Held.LocalPairs.permutationPairAction S R a (e.symm (e x))) = _
  rw [e.symm_apply_apply]

/-- Exact range in plane coordinates; it is not limited to the exhibited GAP actors. -/
theorem planeAction_range
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (e : R ≃* Plane 3) :
    (planeAction S R e).range = (pairAutomizer S R).map (MulAut.congr e).toMonoidHom := by
  rw [planeAction, MonoidHom.range_comp, permutationPairAction_range hrealize]

/-- A two-group action escaping the inner restriction image has a genuinely
outer extending actor in the actual permutation normalizer. A model proof
must still establish the failure of containment, for example by proving
reducibility of every inner action and using the source irreducibility. -/
theorem exists_outer_actor_of_not_le_inner
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (S R : Subgroup Held.He) (D : Subgroup (MulAut R))
    (hD : D ≤ pairAutomizer S R)
    (hnot : ¬ D ≤ (innerPairAction S R).range) :
    ∃ a : Held.LocalPairs.permutationPairStabilizer S R,
      Held.LocalPairs.permutationPairAction S R a ∈ D ∧
      a.val.val ∉ Held.permutationGroup := by
  classical
  by_contra hno
  apply hnot
  intro b hb
  have hr : b ∈ (Held.LocalPairs.permutationPairAction S R).range := by
    rw [permutationPairAction_range hrealize]
    exact hD hb
  obtain ⟨a, ha⟩ := hr
  have hin : a.val.val ∈ Held.permutationGroup := by
    by_contra hout
    exact hno ⟨a, ha ▸ hb, hout⟩
  obtain ⟨g, hg⟩ := (Held.LocalPairs.normalizerAction_mem_inner_iff a.val).mpr hin
  have hga : MulAut.conj g ∈ automorphismPairStabilizer S R := by
    rw [hg]
    exact a.property
  refine ⟨⟨g, hga⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (MulAut.conj g) (x : Held.He) = (b x : Held.He)
  rw [hg, ← ha]
  rfl


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
