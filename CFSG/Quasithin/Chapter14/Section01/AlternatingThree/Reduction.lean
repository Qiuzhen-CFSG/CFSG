module

public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Orbit
public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.SymmetricExclusion
public import Theory.SpecificGroups.Alternating.FourThompsonImage

/-!
# Original 14.1.10 reduced to the faithful two-block action

The actual normal orbit is constructed from the original subnormal A₃
block. Its nontrivial centralizer proves the desired placement and strict
omega-center bound. If the centralizer is trivial, the one-block model
and original Thompson movement force S₄ and contradict the original
maximal-local hypotheses. Thus only the faithful A₄² action remains.
The subsequent finite-image theorem uses O₂(M)≤R≤T in this last case.

Source: Aschbacher--Smith 14.1.10, printed p.978.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
variable {G : Type*} [Group G] [Finite G]

/-- All original ambient branches except the faithful two-block action are discharged. -/
theorem source_faithful_pair_reduction {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (X R : Subgroup M) (hb : ChapterC.IsBlock X) (ha : ChapterC.IsAlternatingBlock X 3)
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆) :
    (M = Mc ∧ 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))) ∨
      let N := conjugateSpanBy X (T.subtype hM.2 : Subgroup M)
      N.Normal ∧ centralizer (N : Set M) = ⊥ ∧ Nonempty (N ≃* AlternatingFourPair.Model) := by
  let N := conjugateSpanBy X (T.subtype hM.2 : Subgroup M)
  obtain ⟨hn,hmodels⟩ := source_cubic_orbit hG T hM X hb ha
  let : N.Normal := hn
  rcases source_centralizer_alternative hG T hM hu N hmodels with hdone | hc
  · exact Or.inl hdone
  rcases hmodels with hsingle | hpair
  · obtain ⟨eN⟩ := hsingle
    obtain ⟨eX⟩ := ha.equiv_alternatingFour
    obtain ⟨e⟩ := AlternatingFourPair.symmetric_four_of_moved_normal N X R eN eX hc hm
    exact (not_symmetric_four_overgroup hG.evenCharacteristic T hM.2 hu hmany e).elim
  · exact Or.inr ⟨hn,hc,hpair⟩

end CFSG.Quasithin.Chapter14.AlternatingThree
