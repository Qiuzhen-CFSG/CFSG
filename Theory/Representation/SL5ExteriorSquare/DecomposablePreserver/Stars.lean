module
public import Theory.Representation.SL5ExteriorSquare.DecomposablePreserver.Adjacency

/-!
# Four-dimensional totally decomposable subspaces are stars

The support planes of nonzero vectors in a totally decomposable subspace
form a Grassmann clique. The common-line alternative places the entire
subspace in a star. The common-three-space alternative places it in the image
of that three-space's exterior square, whose dimension is at most three.
Thus a four-dimensional subspace must be a star.

Source of the clique dichotomy: Meierfrankenfeld–Stellmacher (1993), (1.6),
pp.845–847; this is its specialization to binary exterior squares.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
namespace DecomposablePreserver

noncomputable def exteriorSubspace (H : Submodule (ZMod 2) N) : Submodule (ZMod 2) V :=
  LinearMap.range (exteriorPower.map 2 H.subtype)

theorem finrank_exteriorSubspace_le (H : Submodule (ZMod 2) N) :
    Module.finrank (ZMod 2) (exteriorSubspace H) ≤ (Module.finrank (ZMod 2) H).choose 2 := by
  have h := (exteriorPower.map 2 H.subtype).finrank_range_le
  rwa [exteriorPower.finrank_eq] at h

theorem wedge_mem_exteriorSubspace {H : Submodule (ZMod 2) N} {a b : N}
    (ha : a ∈ H) (hb : b ∈ H) : wedge a b ∈ exteriorSubspace H := by
  refine ⟨exteriorPower.ιMulti (ZMod 2) 2 ![⟨a,ha⟩,⟨b,hb⟩], ?_⟩
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem mem_exteriorSubspace_of_support_le {H : Submodule (ZMod 2) N} {v : V}
    (hv : InExteriorOrbit decomposable v) (h : support v ≤ H) :
    v ∈ exteriorSubspace H := by
  obtain ⟨hv0,a,b,rfl⟩ := (decomposable_iff_wedge v).mp hv
  rw [support_wedge hv0] at h
  exact wedge_mem_exteriorSubspace
    (h (Submodule.subset_span (by simp))) (h (Submodule.subset_span (by simp)))

/-- Every four-space all of whose nonzero vectors are decomposable is a star. -/
theorem eq_star_of_totally_decomposable (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 4)
    (hD : ∀ v ∈ U, v ≠ 0 → InExteriorOrbit decomposable v) :
    ∃ a : N, a ≠ 0 ∧ U = star a := by
  have hU0 : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU
    omega
  obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hnot : ¬ U ≤ Submodule.span (ZMod 2) {u} := by
    intro h
    have hh := Submodule.finrank_mono h
    rw [hU, finrank_span_singleton hu0] at hh
    omega
  obtain ⟨v,hv,hvu⟩ := SetLike.not_le_iff_exists.mp hnot
  have hv0 : v ≠ 0 := fun h => hvu (h ▸ Submodule.zero_mem _)
  have huv : u ≠ v := fun h => hvu (h ▸ Submodule.subset_span (by simp))
  let I := {v : V // v ∈ U ∧ v ≠ 0}
  let W : I → Submodule (ZMod 2) N := fun i => support i.val
  let i : I := ⟨u,hu,hu0⟩
  let j : I := ⟨v,hv,hv0⟩
  have hr (k : I) : Module.finrank (ZMod 2) (W k) = 2 :=
    finrank_support_of_decomposable (hD k.val k.property.1 k.property.2)
  have ha (k l : I) : 2 ≤ Module.finrank (ZMod 2) ↥(W k ⊓ W l) + 1 := by
    apply supports_adjacent (hD k.val k.property.1 k.property.2)
      (hD l.val l.property.1 l.property.2)
    by_cases h0 : k.val + l.val = 0
    · left
      have hn : -l.val = l.val := ZModModule.neg_eq_self _
      exact (eq_neg_of_add_eq_zero_left h0).trans hn
    · exact Or.inr (hD _ (U.add_mem k.property.1 l.property.1) h0)
  have hne : W i ≠ W j := by
    intro h
    exact huv (eq_of_support_eq (hD u hu hu0) (hD v hv hv0) h)
  have hinter := Submodule.rank_intersection_of_adjacent (hr i) (hr j) (ha i j) hne
  have hsup : Module.finrank (ZMod 2) ↥(W i ⊔ W j) = 3 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (W i) (W j)
    rw [hr i,hr j] at hd
    omega
  rcases Submodule.clique_star_or_top W 2 hr ha i j hne with hstar | htop
  · have hcommon : W i ⊓ W j ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hinter
      omega
    obtain ⟨a,ha,ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcommon
    refine ⟨a,ha0,Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
    · intro x hx
      by_cases hx0 : x = 0
      · exact hx0 ▸ Submodule.zero_mem _
      apply (mem_star_iff_mem_support ha0 (hD x hx hx0)).mpr
      exact hstar ⟨x,hx,hx0⟩ ha
    · rw [hU, finrank_star ha0]
  · have hle : U ≤ exteriorSubspace (W i ⊔ W j) := by
      intro x hx
      by_cases hx0 : x = 0
      · exact hx0 ▸ Submodule.zero_mem _
      exact mem_exteriorSubspace_of_support_le (hD x hx hx0) (htop ⟨x,hx,hx0⟩)
    have hd := (Submodule.finrank_mono hle).trans (finrank_exteriorSubspace_le _)
    rw [hU, hsup] at hd
    norm_num at hd

end DecomposablePreserver
end Representation.SL5ExteriorSquare
