module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ExtraspecialReduction
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Central-involution enlargement in the extraspecial centralizer branch

For elementary X, the actual ambient subgroup W = Ω₁(Z(C(X))) contains X,
has the same centralizer, and is normalized by N(X). If C(X) lies in an
extraspecial two-group Q, then W lies in Q and contains its central involution.
The center-orbit argument therefore produces a nontrivial pure subgroup
normalized by N(X), without assuming that the central involution belongs to X.

The native application uses Q = O₂(C(t)) for an actual 2A-involution t of J₄.
At maximal-two-local level the enlarged normalizer equals the original one.
`RadicalCentralizerReduction` retains the resulting whole radical normalizer
and its literal inclusion in the pure-subgroup normalizer.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.3, p.491, the central-involution enlargement and reducibility of the mixed
extraspecial configuration. The hypothesis C(X) ≤ O₂(C(t)) remains the precise
native placement needed from the preceding Figure 2 and isotropic-space
calculation. This module does not assert that placement for arbitrary X or
classify the pure-subgroup normalizers. No intrinsic symmetry premise is needed
for this group-theoretic step.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace Janko4.LocalStructure.ElementaryNormalizerCover
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- An elementary subgroup lies in the central omega of its full centralizer. -/
theorem elementary_le_centralizer_omegaCenter {G : Type*} [Group G]
    (X : Subgroup G) [IsElementaryAbelian 2 X] :
    X ≤ omegaCenterIn (centralizer (X : Set G)) := by
  intro x hx
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨X.le_centralizer hx, fun y hy => (hy x hx).symm,
      elemPow_eq_one_of_isElementaryAbelian x hx⟩

/-- The whole ambient normalizer preserves the canonical enlargement. -/
theorem normalizer_le_centralizer_omegaCenter_normalizer {G : Type*} [Group G]
    (X : Subgroup G) :
    normalizer (X : Set G) ≤
      normalizer (omegaCenterIn (centralizer (X : Set G)) : Set G) :=
  (normalizer_le_normalizer_centralizer X).trans
    (normalizer_le_normalizer_omegaCenterIn _)

/-- The canonical enlargement preserves the full ambient centralizer. -/
theorem centralizer_omegaCenter_centralizer_eq {G : Type*} [Group G]
    (X : Subgroup G) [IsElementaryAbelian 2 X] :
    centralizer (omegaCenterIn (centralizer (X : Set G)) : Set G) =
      centralizer (X : Set G) := by
  apply le_antisymm (centralizer_le (elementary_le_centralizer_omegaCenter X))
  intro c hc w hw
  exact ((mem_omegaCenterIn_iff _ _).mp hw).2.1 c hc |>.symm

/-- Core placement of the full centralizer produces a nontrivial pure subgroup. -/
theorem extraspecial_centralizer_pure_reduction {G : Type*} [Group G]
    (Q X : Subgroup G) [IsExtraspecial 2 Q] [IsElementaryAbelian 2 X]
    (hC : centralizer (X : Set G) ≤ Q)
    (z : Q) (hz : z ∈ center Q) (hz1 : z ≠ 1) :
    ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ omegaCenterIn (centralizer (X : Set G)) ∧
      Y ≤ Q ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set G) ≤ normalizer (Y : Set G) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj (z : G) y := by
  classical
  let W := omegaCenterIn (centralizer (X : Set G))
  have hWQ : W ≤ Q := (map_subtype_le _).trans hC
  have hzC : (z : G) ∈ centralizer (X : Set G) := by
    intro x hx
    exact congrArg (fun a : Q => (a : G))
      (mem_center_iff.mp hz ⟨x, hC (X.le_centralizer hx)⟩)
  have hzW : (z : G) ∈ W := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hzC, ?_, ?_⟩
    · intro c hc
      exact congrArg (fun a : Q => (a : G)) (mem_center_iff.mp hz ⟨c, hC hc⟩)
    · have hs := congrArg (fun a : center Q => (a.val : G))
        (pow_card_eq_one' (x := (⟨z, hz⟩ : center Q)))
      simpa only [IsExtraspecial.center_order_p 2 Q, Subgroup.coe_pow,
        Subgroup.coe_one] using hs
  have hWne : W ≠ ⊥ := by
    intro he
    exact hz1 (Subtype.ext (mem_bot.mp (he ▸ hzW)))
  have hNW : normalizer (X : Set G) ≤ normalizer (W : Set G) :=
    normalizer_le_centralizer_omegaCenter_normalizer X
  by_cases hp : ∀ w ∈ W, w ≠ 1 → IsConj (z : G) w
  · exact ⟨W, hWne, le_rfl, hWQ, inferInstance, hNW, hp⟩
  · push Not at hp
    obtain ⟨w, hw, hw1, hwp⟩ := hp
    obtain ⟨Y, hYne, hYW, hYe, hN, hYp⟩ :=
      extraspecial_pure_reduction Q W hWQ z hz hz1 hzW ⟨w, hw⟩
        (fun he => hw1 (congrArg Subtype.val he)) hwp
    exact ⟨Y, hYne, hYW.le, hYW.le.trans hWQ, hYe, hNW.trans hN, hYp⟩

/-- The native enlargement, with the actual embedded involution-centralizer core. -/
theorem centralizer_in_involution_core_pure_reduction
    (t : Model) (ht : IsConj a t) (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hC : centralizer (X : Set Model) ≤ (centralizer ({t} : Set Model)).pCoreIn 2) :
    ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ omegaCenterIn (centralizer (X : Set Model)) ∧
      Y ≤ (centralizer ({t} : Set Model)).pCoreIn 2 ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp ht
  let Q := firstCore.map (MulAut.conj g).toMonoidHom
  let e : firstCore ≃* Q := firstCore.equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv e firstCore_extraspecial
  let z : Q := e ⟨a, a_mem_firstCore⟩
  have hzc : z ∈ center Q := (Subgroup.centerCongr e ⟨⟨a, a_mem_firstCore⟩,
    a_central_in_firstCore⟩).property
  have hz1 : z ≠ 1 := by
    intro hh
    have ha1 : a = 1 := congrArg (fun x : firstCore => (x : Model))
      (e.injective (hh.trans (map_one e).symm))
    have ho := orderOf_a
    rw [ha1, orderOf_one] at ho
    contradiction
  have hQt : Q = (centralizer ({t} : Set Model)).pCoreIn 2 := by
    dsimp only [Q]
    rw [firstCore_conjugate, show MulAut.conj g a = t from hg]
  have hzclass : IsConj a (z : Model) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨Y, hYne, hYW, hYQ, hYe, hNY, hYp⟩ :=
    extraspecial_centralizer_pure_reduction Q X (hQt ▸ hC) z hzc hz1
  exact ⟨Y, hYne, hYW, hQt ▸ hYQ, hYe, hNY,
    fun y hy hy1 => hzclass.trans (hYp y hy hy1)⟩

/-- Maximality among two-locals preserves the whole normalizer after reduction. -/
theorem maximal_normalizer_centralizer_in_involution_core_reduction
    (t : Model) (ht : IsConj a t) (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hC : centralizer (X : Set Model) ≤ (centralizer ({t} : Set Model)).pCoreIn 2)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ omegaCenterIn (centralizer (X : Set Model)) ∧
      Y ≤ (centralizer ({t} : Set Model)).pCoreIn 2 ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) = normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
  obtain ⟨Y, hYne, hYW, hYQ, hYe, hNY, hYp⟩ :=
    centralizer_in_involution_core_pure_reduction t ht X hC
  let := hYe
  exact ⟨Y, hYne, hYW, hYQ, hYe,
    hM.eq_of_le ⟨Y, hYne, IsElementaryAbelian.isPGroup 2 Y, rfl⟩ hNY, hYp⟩

end Janko4.LocalStructure.ElementaryNormalizerCover
