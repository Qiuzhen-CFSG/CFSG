module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.PairwiseRecognition.Lifting
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.PairwiseRecognition.Inputs
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The generating pair in the exceptional S₆ quotient

A surjection with kernel in the common Sylow subgroup preserves both local
indices, and maps the two overgroups to a generating pair. Residual image
transport identifies the image factors with the two-residuals of that pair.
Together with `Lifting`, this reduces the paragraph following 15.4.23 to a
finite permutation-group recognition theorem, while retaining the actual
quotient map and its kernel.

Source: Aschbacher–Smith, printed p.1165. No A₄ or D₈ identification is
asserted in this reduction module.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type*} [Group G] [Finite G] {d : Geometry G} (h : LocalData d)
include h

omit h in
private theorem residual_subgroupOf {H L R : Subgroup G} (hLH : L ≤ H)
    (hr : (pResidual 2 L).map L.subtype = R) :
    (pResidual 2 (L.subgroupOf H)).map (L.subgroupOf H).subtype = R.subgroupOf H := by
  have hRH : R ≤ H := by
    rw [← hr]
    exact (map_subtype_le _).trans hLH
  apply Subgroup.map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le hRH, map_embedded_pResidual,
    map_subgroupOf_eq_of_le hLH, hr]

/-- Each image factor is the actual two-residual of the image overgroup. -/
theorem LocalData.quotient_residual_G₁ (i j : Bool) (f : d.I i j →* Equiv.Perm (Fin 6)) :
    (pResidual 2 (((d.G₁ i).subgroupOf (d.I i j)).map f)).map
        (((d.G₁ i).subgroupOf (d.I i j)).map f).subtype =
      ((d.X i).subgroupOf (d.I i j)).map f := by
  rw [← map_embedded_pResidual,
    residual_subgroupOf (H := d.I i j) le_sup_left (h.residual_G₁ i)]

theorem LocalData.quotient_residual_G₂ (i j : Bool) (f : d.I i j →* Equiv.Perm (Fin 6)) :
    (pResidual 2 (((d.G₂ j).subgroupOf (d.I i j)).map f)).map
        (((d.G₂ j).subgroupOf (d.I i j)).map f).subtype =
      ((d.Y j).subgroupOf (d.I i j)).map f := by
  rw [← map_embedded_pResidual,
    residual_subgroupOf (H := d.I i j) le_sup_right (h.residual_G₂ j)]

/-- All finite-model input conditions follow from the local data and a
surjection whose kernel lies in the common Sylow subgroup. -/
theorem LocalData.quotient_pair_inputs (i j : Bool)
    (f : d.I i j →* Equiv.Perm (Fin 6)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (h.sylow i j : Subgroup (d.I i j))) :
    let T := ((h.sylow i j).mapSurjective hf : Subgroup (Equiv.Perm (Fin 6)))
    let H₁ := ((d.G₁ i).subgroupOf (d.I i j)).map f
    let H₂ := ((d.G₂ j).subgroupOf (d.I i j)).map f
    T ≤ H₁ ∧ T ≤ H₂ ∧ T.relIndex H₁ = 3 ∧ T.relIndex H₂ = 3 ∧ H₁ ⊔ H₂ = ⊤ := by
  let S := (h.sylow i j : Subgroup (d.I i j))
  let P₁ := (d.G₁ i).subgroupOf (d.I i j)
  let P₂ := (d.G₂ j).subgroupOf (d.I i j)
  have hS₁ : S ≤ P₁ := by
    intro x hx
    have ht : (x : G) ∈ d.T₀ := by
      rw [← h.sylow_image i j]
      exact ⟨x, hx, rfl⟩
    exact (show d.T₀ ≤ d.G₁ i from le_sup_right) ht
  have hS₂ : S ≤ P₂ := by
    intro x hx
    have ht : (x : G) ∈ d.T₀ := by
      rw [← h.sylow_image i j]
      exact ⟨x, hx, rfl⟩
    exact (show d.T₀ ≤ d.G₂ j from le_sup_right) ht
  have hi₁ : S.relIndex P₁ = 3 := by
    rw [← relIndex_map_map_of_injective S P₁ (d.I i j).subtype_injective]
    rw [h.sylow_image, map_subgroupOf_eq_of_le (show d.G₁ i ≤ d.I i j from le_sup_left)]
    exact h.relIndex_T₀_G₁ i
  have hi₂ : S.relIndex P₂ = 3 := by
    rw [← relIndex_map_map_of_injective S P₂ (d.I i j).subtype_injective]
    rw [h.sylow_image, map_subgroupOf_eq_of_le (show d.G₂ j ≤ d.I i j from le_sup_right)]
    exact h.relIndex_T₀_G₂ j
  refine ⟨map_mono hS₁, map_mono hS₂, ?_, ?_, ?_⟩
  · change (S.map f).relIndex (P₁.map f) = 3
    rw [relIndex_map_map, sup_of_le_left hk, sup_of_le_left (hk.trans hS₁)]
    exact hi₁
  · change (S.map f).relIndex (P₂.map f) = 3
    rw [relIndex_map_map, sup_of_le_left hk, sup_of_le_left (hk.trans hS₂)]
    exact hi₂
  · rw [← Subgroup.map_sup, ← subgroupOf_sup
      (show d.G₁ i ≤ d.I i j from le_sup_left)
      (show d.G₂ j ≤ d.I i j from le_sup_right)]
    change ((d.I i j).subgroupOf (d.I i j)).map f = ⊤
    rw [subgroupOf_self, map_top_of_surjective f hf]

end CFSG.Quasithin.Chapter15.Section04.Source
