/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/IndexTwoInvariantNormals.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.InvolutiveNormalFactors
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index

/-!
# Invariant normal subgroups at index two

An involution outside an index-two subgroup gives a two-coset normal form.
Normal subgroups invariant under its conjugation lift to normal subgroups of
the ambient group.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/IndexTwoInvariantNormals.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project import.
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace Atlas.GroupTheory

/-- An involution outside an index-two subgroup gives the two explicit cosets. -/
theorem index_two_involution_normal_form {J : Type*} [Group J]
    (K : Subgroup J) (hi : K.index = 2) (d : J) (hd : d ∉ K) (hdd : d*d=1)
    (g : J) : ∃ k : K, g = k.val ∨ g = k.val*d := by
  by_cases hg : g ∈ K
  · exact ⟨⟨g,hg⟩,Or.inl rfl⟩
  · have hgd : g*d ∈ K := (K.mul_mem_iff_of_index_two hi).mpr (by simp [hg,hd])
    refine ⟨⟨g*d,hgd⟩,Or.inr ?_⟩
    simp [mul_assoc,hdd]

/-- A normal subgroup of an index-two subgroup stable under the outside
involution is normal in the full group. -/
theorem normal_map_of_index_two_invariant {J : Type*} [Group J]
    (K : Subgroup J) [K.Normal] (hi : K.index=2) (d : J) (hd : d ∉ K)
    (hdd : d*d=1) (H : Subgroup K) [H.Normal]
    (hstable : H.map (MulAut.conjNormal d).toMonoidHom = H) :
    (H.map K.subtype).Normal := by
  constructor
  intro n hn g
  obtain ⟨n,hn,rfl⟩ := hn
  obtain ⟨k,hk | hk⟩ := index_two_involution_normal_form K hi d hd hdd g
  · subst g
    exact ⟨k*n*k⁻¹, (inferInstance : H.Normal).conj_mem n hn k, rfl⟩
  · subst g
    have han : MulAut.conjNormal d n ∈ H := by
      rw [← hstable]
      exact ⟨n,hn,rfl⟩
    refine ⟨k*(MulAut.conjNormal d n)*k⁻¹,
      (inferInstance : H.Normal).conj_mem _ han k, ?_⟩
    change k.val * (d*n.val*d⁻¹) * k.val⁻¹ = (k.val*d)*n.val*(k.val*d)⁻¹
    simp only [mul_inv_rev,mul_assoc]

/-- Minimality among full-group normal subgroups becomes minimality among
normal subgroups invariant under the outside involution. -/
theorem index_two_invariant_normal_dichotomy {J : Type*} [Group J]
    (K : Subgroup J) [K.Normal] (hi : K.index=2) (d : J) (hd : d ∉ K)
    (hdd : d*d=1)
    (hmin : ∀ L : Subgroup J, L.Normal → L = ⊥ ∨ K ≤ L)
    (H : Subgroup K) (hH : H.Normal)
    (hstable : H.map (MulAut.conjNormal d).toMonoidHom = H) : H=⊥ ∨ H=⊤ := by
  letI := hH
  have hL := normal_map_of_index_two_invariant K hi d hd hdd H hstable
  rcases hmin (H.map K.subtype) hL with h | h
  · left
    apply bot_unique
    intro n hn
    have he : n.val = 1 := by
      have hm : n.val ∈ H.map K.subtype := ⟨n,hn,rfl⟩
      simpa [h] using hm
    exact Subtype.ext he
  · right
    apply top_unique
    intro n _
    obtain ⟨m,hm,he⟩ := h n.prop
    have : m=n := Subtype.ext he
    simpa [this] using hm

end Atlas.GroupTheory
