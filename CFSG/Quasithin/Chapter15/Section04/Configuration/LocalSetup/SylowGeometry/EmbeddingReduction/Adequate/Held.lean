module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.InvariantResidual
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowPointwise

/-!
# The residual identity for the retained invariant Held component

The proved full permutation realization and normalizer quotient calculation
make the actual Held outer group a two-group. Rank two of the genuine
component quotient then excludes extra three-elements in its centralizer.
The component index is prime to three and therefore contains O^{3′}(H).
The existing two-perfect normal-generation argument gives the opposite
containment for the original X-normal closure.

These are consequences of actual local hypotheses and a retained Held model,
not assumptions in the adequate intrinsic theorem. No Held multiplier or
recognition from order is used. Source: A.3.18 and the residual step in
15.4.20, pp.51--52,1163--1164.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u

/-- Full realization and the checked normalizer quotient bound control the
outer group of every specified Held model. -/
theorem held_outer_prime_to_three {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* Held.He) : Nat.Coprime 3 (Nat.card (MulAut.Outer Q)) := by
  have hp : IsPGroup 2 (MulAut.Outer Held.He) :=
    Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2
      Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv, hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

/-- The literal Held quotient is centerless independently of any simplicity
recognition for the concrete carrier. -/
theorem held_model_center_bot {Q : Type*} [Group Q]
    (e : Q ≃* Held.He) : center Q = ⊥ := by
  apply eq_bot_iff.mpr
  intro q hq
  have he : e q ∈ center Held.He := (centerCongr e ⟨q, hq⟩).property
  rw [Held.LocalPairs.center_eq_bot] at he
  exact e.injective (mem_bot.mp he |>.trans (map_one e).symm)

variable {G : Type u} [Group G] [Finite G]
open Chapter1 Chapter1.XiEmbedding.InvariantThree

/-- The invariant Held component contains the actual three-prime residual,
using SQTK rank control and the proved full outer-group calculation. -/
theorem held_residual_le {κ : GroupClass.{u}} {U X P H L : Subgroup G}
    (hH : IsSQTK κ H) (h : XiEmbedding.LocalInput 3 U X P H)
    (hL : L ∈ cComponentsIn H) (hn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (e : XiQuotient L ≃* Held.He) :
    (primeToResidual 3 H).map H.subtype ≤ L := by
  let N := L.subgroupOf H
  let _ : N.Normal := hn
  let f : (N ⧸ pCore 2 N) ≃* Held.He :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL.1) (pCore_map_iso 2 _)).trans e
  have hr : 2 ≤ primeRank 3 (N ⧸ pCore 2 N) := by
    rw [primeRank_equiv 3
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL.1) (pCore_map_iso 2 _))]
    exact (component_quotient_rank h hH.stronglyQuasithin hL.1
      ((le_sup_right.trans h.complement.le).trans hXL)).2.ge
  have hi := cComponent_index_coprime_three_of_quotient N hL.2
    (held_model_center_bot f) hr (hH.stronglyQuasithin 3 (by decide) (by decide))
    (held_outer_prime_to_three f)
  exact (map_mono (f := H.subtype) (primeToResidual_le N hi)).trans_eq
    (map_subgroupOf_eq_of_le hL.1)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
