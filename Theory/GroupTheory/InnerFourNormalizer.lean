module
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The inner four and its Sylow normalizer

For a center-free group, an inner cubic actor with a Klein-four two-core
pulls back to a literal four-group. Its normalizer index in any Sylow whose
inner image lies in the prescribed actor two-group inherits the given bound.
A Sylow subgroup of a component normalizer always contains the inner image
of some Sylow of the component. These are the precise transports used in
the paired-cubic inspection, Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- The literal inner four pulled back from the cubic actor inherits the
actual Sylow normalizer bound; no absorption of the ambient A₄ is assumed. -/
theorem inner_four_of_actor_normalizer_index
    {X : Type*} [_root_.Group X] [Finite X] (hz : center X = ⊥)
    (B A : Subgroup (MulAut X)) (hB : B ≤ (MulAut.conj : X →* MulAut X).range)
    [IsKleinFour (B.pCoreIn 2)] (P : Sylow 2 X)
    (hPA : (P : Subgroup X).map MulAut.conj ≤ A)
    (hindex : (normalizer (B : Set (MulAut X))).relIndex A ≤ 2) :
    ∃ V : Subgroup X, IsKleinFour V ∧
      V.map MulAut.conj = B.pCoreIn 2 ∧
      ((normalizer (V : Set X)).subgroupOf P).index ≤ 2 := by
  let f : X →* MulAut X := MulAut.conj
  have hf : Function.Injective f :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let U := B.pCoreIn 2
  have hU : U ≤ f.range := (pCoreIn_le 2 B).trans hB
  let V := U.comap f
  have hmap : V.map f = U := map_comap_eq_self hU
  let e : V ≃* U := (V.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)
  have hV : IsKleinFour V := {
    card_four := (Nat.card_congr e.toEquiv).trans (IsKleinFour.card_four (G := U))
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans (IsKleinFour.exponent_two (G := U)) }
  have hnu : normalizer (B : Set (MulAut X)) ≤
      normalizer (U : Set (MulAut X)) := by
    exact normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  refine ⟨V,hV,hmap,?_⟩
  change (normalizer (U.comap f : Set X)).relIndex (P : Subgroup X) ≤ 2
  rw [←comap_normalizer_eq_of_le_range hU,relIndex_comap]
  exact (relIndex_le_of_le_left hnu index_ne_zero_of_finite).trans
    ((relIndex_le_of_le_right hPA index_ne_zero_of_finite).trans hindex)

end Theory.GroupTheory

namespace Subgroup
variable {H : Type*} [Group H] [Finite H]
/-- The intrinsic Sylow is the literal intersection with the selected normalizer Sylow. -/
theorem exists_sylow_eq_comap_and_inner_le_normalizer_image (K : Subgroup H)
    (S : Sylow 2 (normalizer (K : Set H))) :
    ∃ P : Sylow 2 K, (P : Subgroup K) =
      (S : Subgroup (normalizer (K : Set H))).comap (inclusion K.le_normalizer) ∧
      (P : Subgroup K).map MulAut.conj ≤
      (S : Subgroup (normalizer (K : Set H))).map K.normalizerMonoidHom := by
  let N := normalizer (K : Set H)
  let E := K.subgroupOf N
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal E
  let e : E ≃* K := subgroupOfEquivOfLe K.le_normalizer
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_,?_⟩
  · ext k
    constructor
    · rintro ⟨v,hv,rfl⟩
      rw [hP] at hv
      exact hv
    · intro hk
      refine ⟨e.symm k,?_,e.apply_symm_apply k⟩
      rw [hP]
      exact hk
  · rintro a ⟨k,hk,rfl⟩
    obtain ⟨v,hv,rfl⟩ := hk
    refine ⟨(v : N),?_,?_⟩
    · rw [hP] at hv
      exact hv
    · apply MulEquiv.ext
      intro x
      rfl
/-- The canonical component-normalizer action contains an intrinsic Sylow inner image. -/
theorem exists_sylow_inner_le_normalizer_image (K : Subgroup H)
    (S : Sylow 2 (normalizer (K : Set H))) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map MulAut.conj ≤
      (S : Subgroup (normalizer (K : Set H))).map K.normalizerMonoidHom := by
  obtain ⟨P,_,hP⟩ := K.exists_sylow_eq_comap_and_inner_le_normalizer_image S
  exact ⟨P,hP⟩
end Subgroup
