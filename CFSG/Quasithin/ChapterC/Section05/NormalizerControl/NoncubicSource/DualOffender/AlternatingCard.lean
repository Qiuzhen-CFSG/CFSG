module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Quadratic
/-!
# The A₅ conjugate actor and displacement orders

The original module has order sixteen and the C.5.6 fixed plane has order
four. The conjugate module has the same order, so its faithful image and
its displacement both have rank two. No new pair model is assumed.
Source: Aschbacher–Smith C.5.6(2) and C.5.13, printed pp.156 and162.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource
variable {G : Type*} [Group G] [Finite G] {K T L : Subgroup G}
/-- The actual A₅ source actor and displacement each have four elements. -/
theorem alternating_pair_card (h : AlternatingPairSetup T K L) {x : G}
    (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
    let E := sourceModule K ⊓ B
    Nat.card E = 4 ∧ E.relIndex B = 4 := by
  let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := sourceModule K ⊓ B
  have he : Nat.card E = 4 := by
    change Nat.card (sourceModule K ⊓ B : Subgroup G) = _
    rw [← (h.commutator_eq_fixed x hx hnc).2,(h.commutator_eq_fixed x hx hnc).1]
    exact h.conjugate_fixed_card x hx hnc
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) E B bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,he,card_map_of_injective (MulAut.conj x⁻¹).injective,
    h.module_card] at hm
  refine ⟨he,?_⟩
  change E.relIndex B = 4
  omega
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
