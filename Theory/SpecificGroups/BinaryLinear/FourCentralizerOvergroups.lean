module

public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups.Directions

/-!
# Proper overgroups of an incident binary line–hyperplane stabilizer

Let w lie in the kernel of a linear form f on F₂⁴. Every proper overgroup
of the common stabilizer of ⟨w⟩ and ker(f) lies in one of those two
stabilizers.

For such an overgroup K, its full transvection directions form a proper
K-invariant subspace D containing w. If D contains a vector outside ker(f),
the transvections x ↦ x + f(x)u, for u ∈ ker(f), force D to be the whole
space. Otherwise D lies in ker(f). If D is larger than ⟨w⟩, transvections
fixing w and preserving ker(f) force every vector of ker(f) into D. Hence
D is either ⟨w⟩ or ker(f), giving the required cover.

This is the intrinsic linear-group calculation used for Aschbacher–Smith
2.3.9(7)(g), printed pp.525–526 of `refs/quasithin.pdf`. Over F₂ the common
stabilizer is the centralizer of the rank-one transvection with coordinates
(w, f); the chapter adapter supplies that established identity.
-/

public section

namespace BinaryLinear.FourCentralizerOvergroups

local notation "Vec" => (Fin 4 → ZMod 2)

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem line_mem_of_fix (g : GL Vec) (w : Vec) (hw : g w = w) :
    g ∈ parabolic (Submodule.span (ZMod 2) {w}) := by
  intro v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    exact Submodule.mem_span_singleton.mpr ⟨a, g.injective (by rwa [map_smul, hw])⟩
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hw]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w)

private theorem transvection_mem_flag (w u : Vec)
    (f q : Vec →ₗ[ZMod 2] ZMod 2) (hfu : f u = 0) (hqw : q w = 0) (hqu : q u = 0) :
    transvection u q hqu ∈ parabolic (Submodule.span (ZMod 2) {w}) ⊓ parabolic f.ker := by
  constructor
  · apply line_mem_of_fix
    change w + q w • u = w
    simp [hqw]
  · intro v
    change f (v + q v • u) = 0 ↔ f v = 0
    simp [hfu]

/-- Every proper overgroup of the incident line–hyperplane stabilizer in
GL₄(2) preserves one of the two subspaces. -/
theorem flag_overgroup_cover (w : Vec) (f : Vec →ₗ[ZMod 2] ZMod 2)
    (hfw : f w = 0) (K : Subgroup (GL Vec))
    (hC : parabolic (Submodule.span (ZMod 2) {w}) ⊓ parabolic f.ker ≤ K)
    (hK : K ≠ ⊤) :
    K ≤ parabolic (Submodule.span (ZMod 2) {w}) ∨ K ≤ parabolic f.ker := by
  classical
  let D := directions K
  have hwD : w ∈ D := by
    intro q hq
    exact hC (transvection_mem_flag w w f q hfw hq hq)
  have hstable {g : GL Vec} (hg : g ∈ K) {v : Vec} (hv : v ∈ D) : g v ∈ D :=
    (le_parabolic_directions K hg v).mpr hv
  have hproper : D ≠ ⊤ := fun hD => hK (eq_top_of_directions_eq_top K hD)
  have hDH : D ≤ f.ker := by
    intro v hv
    by_contra hvf
    have hfv : f v = 1 := scalar_one hvf
    have hHD : f.ker ≤ D := by
      intro u hu
      have hg := hC (transvection_mem_flag w u f f hu hfw hu)
      have hh := hstable hg hv
      change v + f v • u ∈ D at hh
      rw [hfv, one_smul] at hh
      simpa only [add_sub_cancel_left] using D.sub_mem hh hv
    apply hproper
    apply top_unique
    intro x _
    have hx : x - f x • v ∈ f.ker := by
      change f (x - f x • v) = 0
      simp [hfv]
    simpa only [sub_add_cancel] using D.add_mem (hHD hx) (D.smul_mem (f x) hv)
  by_cases hDl : D ≤ Submodule.span (ZMod 2) {w}
  · have hD : D = Submodule.span (ZMod 2) {w} :=
      le_antisymm hDl ((Submodule.span_singleton_le_iff_mem w D).mpr hwD)
    exact Or.inl (by simpa only [← hD] using le_parabolic_directions K)
  · obtain ⟨v, hv, hvl⟩ := SetLike.not_le_iff_exists.mp hDl
    have hHD : f.ker ≤ D := by
      intro u hu
      by_contra huD
      have hvwu : v ∉ Submodule.span (ZMod 2) {w, u} := by
        intro hvwu
        obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hvwu
        by_cases hb : b = 0
        · apply hvl
          exact Submodule.mem_span_singleton.mpr ⟨a, by simpa [hb] using he⟩
        · have hb1 := scalar_one hb
          apply huD
          have hh : u = v - a • w := by rw [← he, hb1, one_smul, add_sub_cancel_left]
          rw [hh]
          exact D.sub_mem hv (D.smul_mem a hwD)
      obtain ⟨q, hqv, hq⟩ := Submodule.exists_le_ker_of_notMem hvwu
      have hqw : q w = 0 := hq (Submodule.subset_span (by simp))
      have hqu : q u = 0 := hq (Submodule.subset_span (by simp))
      have hh := hstable (hC (transvection_mem_flag w u f q hu hqw hqu)) hv
      change v + q v • u ∈ D at hh
      rw [scalar_one hqv, one_smul] at hh
      exact huD (by simpa only [add_sub_cancel_left] using D.sub_mem hh hv)
    have hD : D = f.ker := le_antisymm hDH hHD
    exact Or.inr (by simpa only [← hD] using le_parabolic_directions K)

end BinaryLinear.FourCentralizerOvergroups

end
