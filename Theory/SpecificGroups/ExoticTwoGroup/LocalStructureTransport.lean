module

public import Theory.SpecificGroups.ExoticTwoGroup.LocalStructure
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Conj

/-!
# Transport of the exotic local structure

An equivalence preserving the six generators preserves the core, the normal
four and its even centralizer. It also transports involution classes and
centralizer cardinalities. Restricting the equivalence to each centralizer
transports the characteristic subgroup and its ambient cyclic image.

This allows the presentation calculations of Janko–Thompson, Math. Z. 113
(1970), p.396, to be proved once in a concrete model and then used for every
marked presentation.
-/

namespace ExoticTwoGroup.Presentation
open Subgroup
variable {P Q : Type*} [Group P] [Group Q]

private theorem map_centralizer (e : P ≃* Q) (s : Set P) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm (map_centralizer_le_centralizer_image s e.toMonoidHom)
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  intro x hx
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hy (e x) ⟨x,hx,rfl⟩

private def centralizerEquiv (e : P ≃* Q) (x : P) :
    centralizer ({x} : Set P) ≃* centralizer ({e x} : Set Q) where
  toFun y := ⟨e y, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' y z := Subtype.ext (e.map_mul y z)

private theorem characteristic_map (e : P ≃* Q) (K : Subgroup P)
    (hK : K.Characteristic) : (K.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨e.symm (f (e y)), characteristic_iff_le_comap.mp hK
    (e.trans (f.trans e.symm)) hy, e.apply_symm_apply _⟩

private theorem characteristic_line_map (e : P ≃* Q) (x z : P)
    (h : ∃ K : Subgroup (centralizer ({x} : Set P)), K.Characteristic ∧
      K.map (centralizer ({x} : Set P)).subtype = zpowers z) :
    ∃ K : Subgroup (centralizer ({e x} : Set Q)), K.Characteristic ∧
      K.map (centralizer ({e x} : Set Q)).subtype = zpowers (e z) := by
  obtain ⟨K,hK,he⟩ := h
  let f := centralizerEquiv e x
  refine ⟨K.map f.toMonoidHom, characteristic_map f K hK, ?_⟩
  rw [map_map]
  change K.map (e.toMonoidHom.comp (centralizer ({x} : Set P)).subtype) = _
  rw [← map_map, he, MonoidHom.map_zpowers]
  rfl

/-- Local structure is invariant under an equivalence preserving the six marks. -/
public theorem LocalStructure.of_equiv (d : ExoticTwoGroup.Presentation P)
    (c : ExoticTwoGroup.Presentation Q) (e : P ≃* Q)
    (ha : e d.a = c.a) (hb : e d.b = c.b)
    (hg₁ : e d.g₁ = c.g₁) (hg₂ : e d.g₂ = c.g₂)
    (ht : e d.t = c.t) (hz₀ : e d.z₀ = c.z₀)
    (h : d.LocalStructure) : c.LocalStructure := by
  have hz : e d.centralInvolution = c.centralInvolution := by
    simp only [centralInvolution, map_mul, map_pow, ha, hb]
  have hcore : d.core.map e.toMonoidHom = c.core := by
    simp only [core, MonoidHom.map_closure, Set.image_insert_eq,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, ha, hb, hg₁, hg₂]
  have heven : d.evenSubgroup.map e.toMonoidHom = c.evenSubgroup := by
    simp only [evenSubgroup, MonoidHom.map_closure, Set.image_insert_eq,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, ha, hb, hg₁, hg₂, hz₀]
  have hfour : d.four.map e.toMonoidHom = c.four := by
    simp only [four, MonoidHom.map_closure, Set.image_insert_eq,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, map_pow, ha, hb]
  have hmem (x : P) : e x ∈ c.evenSubgroup ↔ x ∈ d.evenSubgroup := by
    rw [← heven]
    exact mem_map_iff_mem e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hz, e.orderOf_eq]
    exact h.central_order
  · rw [← hz]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp h.central_mem x)
  · rw [← ht, e.orderOf_eq]
    exact h.t_order
  · rw [← hz₀, e.orderOf_eq]
    exact h.z₀_order
  · rw [← heven]
    exact (index_map_of_bijective (f := e.toMonoidHom) e.bijective _).trans h.even_index
  · rw [← heven, h.even_eq_centralizer, map_centralizer]
    exact congrArg centralizer (congrArg (fun H : Subgroup Q => (H : Set Q)) hfour)
  · intro y hy hyD
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [e.orderOf_eq] at hy
    rcases h.even_classes x hy ((hmem x).mp hyD) with hx | hx
    · left
      rw [← hcore]
      exact mem_map_of_mem e.toMonoidHom hx
    · right
      simpa only [MulEquiv.coe_toMonoidHom, ht,hz₀] using e.toMonoidHom.map_isConj hx
  · intro y hy hyD
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [e.orderOf_eq] at hy
    rcases h.odd_classes x hy (fun hx => hyD ((hmem x).mpr hx)) with hx | hx
    · left
      simpa only [MulEquiv.coe_toMonoidHom, ht] using e.toMonoidHom.map_isConj hx
    · right
      simpa only [MulEquiv.coe_toMonoidHom, map_mul,ht,hz₀] using e.toMonoidHom.map_isConj hx
  · rw [← ht, hmem]
    exact h.t_not_even
  · rw [← hz₀, hmem]
    exact h.z₀_mem_even
  · rw [← ht, ← Nat.card_congr (centralizerEquiv e d.t).toEquiv]
    exact h.t_centralizer_card
  · rw [← ht, ← hz₀, ← map_mul, ← Nat.card_congr (centralizerEquiv e (d.t*d.z₀)).toEquiv]
    exact h.tz₀_centralizer_card
  · rw [← hz₀, ← Nat.card_congr (centralizerEquiv e d.z₀).toEquiv]
    exact h.z₀_centralizer_card
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← ht, ← hz]
      exact characteristic_line_map e _ _ (h.characteristic_line d.t (by simp))
    · rw [← hz₀, ← hz]
      exact characteristic_line_map e _ _ (h.characteristic_line d.z₀ (by simp))

end ExoticTwoGroup.Presentation
