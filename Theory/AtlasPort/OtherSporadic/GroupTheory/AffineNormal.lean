/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/AffineNormal.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

/-!
# AffineNormal

Faithful irreducible affine semidirect products with simple linear part have restricted normal subgroups.
Intersecting with translations and taking the linear image gives the alternatives.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/AffineNormal.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
open SemidirectProduct

variable {U B : Type*} [CommGroup U] [Group B] (φ : B →* MulAut U)

theorem affine_centralizer (faithful : Function.Injective φ) :
    Subgroup.centralizer ((inl : U →* U ⋊[φ] B).range : Set (U ⋊[φ] B)) =
      (inl : U →* U ⋊[φ] B).range := by
  ext x
  constructor
  · intro hx
    have hr : φ x.right = 1 := by
      ext u
      have h := congrArg SemidirectProduct.left
        (Subgroup.mem_centralizer_iff.mp hx (inl u) ⟨u,rfl⟩)
      apply mul_left_cancel (a := x.left)
      simpa only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply, mul_comm u] using h.symm
    have he : x.right = 1 := faithful (hr.trans (map_one φ).symm)
    exact ⟨x.left, by ext <;> simp [he]⟩
  · rintro ⟨u,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨v,rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]

theorem affine_normal_subgroups [IsSimpleGroup B]
    (faithful : Function.Injective φ)
    (irreducible : ∀ V : Subgroup U,
      (∀ b u, u ∈ V → φ b u ∈ V) → V = ⊥ ∨ V = ⊤)
    (W : Subgroup (U ⋊[φ] B)) [W.Normal] :
    W = ⊥ ∨ W = (inl : U →* U ⋊[φ] B).range ∨ W = ⊤ := by
  have stable : ∀ b u, u ∈ W.comap inl → φ b u ∈ W.comap inl := by
    intro b u hu
    change inl (φ b u) ∈ W
    rw [inl_aut]
    simpa only [map_inv] using (inferInstance : W.Normal).conj_mem (inl u) hu (inr b)
  rcases irreducible (W.comap inl) stable with hz | hall
  · left
    have hcentral : W ≤ Subgroup.centralizer
        ((inl : U →* U ⋊[φ] B).range : Set (U ⋊[φ] B)) := by
      intro w hw
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨u,rfl⟩
      let c : U ⋊[φ] B := inl u * w * (inl u)⁻¹ * w⁻¹
      have hcW : c ∈ W := W.mul_mem ((inferInstance : W.Normal).conj_mem w hw (inl u)) (W.inv_mem hw)
      have hcr : c.right = 1 := by simp [c]
      have hcl : inl c.left = c := by ext <;> simp [hcr]
      have hcz : c.left ∈ W.comap inl := by change inl c.left ∈ W; rwa [hcl]
      rw [hz] at hcz
      have hc1 : c = 1 := by rw [← hcl, show c.left = 1 from hcz, map_one]
      change inl u * w * (inl u)⁻¹ * w⁻¹ = 1 at hc1
      calc
        inl u * w = (inl u * w * (inl u)⁻¹ * w⁻¹) * w * inl u := by group
        _ = w * inl u := by rw [hc1]; simp
    rw [affine_centralizer φ faithful] at hcentral
    apply le_antisymm _ bot_le
    intro w hw
    obtain ⟨u,rfl⟩ := hcentral hw
    have hu : u ∈ W.comap inl := hw
    rw [hz] at hu
    simp [show u = 1 from hu]
  · right
    have hU : (inl : U →* U ⋊[φ] B).range ≤ W := by
      rintro _ ⟨u,rfl⟩
      have hu : u ∈ W.comap inl := by rw [hall]; trivial
      exact hu
    let : (W.map (rightHom : U ⋊[φ] B →* B)).Normal :=
      (inferInstance : W.Normal).map _ rightHom_surjective
    rcases (inferInstance : (W.map (rightHom : U ⋊[φ] B →* B)).Normal).eq_bot_or_eq_top
        with hb | ht
    · left
      apply le_antisymm _ hU
      intro w hw
      have hr : w.right ∈ W.map (rightHom : U ⋊[φ] B →* B) := ⟨w,hw,rfl⟩
      rw [hb] at hr
      exact ⟨w.left, by ext <;> simp [show w.right = 1 from hr]⟩
    · right
      apply top_unique
      intro x _
      have hx : x.right ∈ W.map (rightHom : U ⋊[φ] B →* B) := by rw [ht]; trivial
      obtain ⟨w,hw,he⟩ := hx
      have hu : x * w⁻¹ ∈ (inl : U →* U ⋊[φ] B).range :=
        ⟨(x*w⁻¹).left, by ext <;> simp [show w.right = x.right from he]⟩
      simpa using W.mul_mem (hU hu) hw

end Atlas.GroupTheory
