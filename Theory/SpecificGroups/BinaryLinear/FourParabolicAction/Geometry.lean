module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rigidity and conjugacy of binary subspace stabilizers

The stabilizer of a nonzero proper subspace has exactly one such invariant subspace.
Rank-one transvections first force the defining subspace into any nonzero
invariant subspace, then force every larger invariant subspace to be the whole
space. In finite dimension, an isomorphism between subspaces of equal dimension
extends to the ambient space, giving transitivity on each Grassmannian.

These intrinsic facts support the end-node argument for PSL₄(2) in
Aschbacher–Smith 2.3.9(7)(g), printed pp.525–526 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace BinaryLinear.FourParabolicAction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem transvection_stabilizes {W : Submodule (ZMod 2) V}
    {w : V} {f : V →ₗ[ZMod 2] ZMod 2} (hfw : f w = 0)
    (h : w ∈ W ∨ W ≤ f.ker) : transvection w f hfw ∈ parabolic W := by
  intro v
  change v + f v • w ∈ W ↔ v ∈ W
  rcases h with hw | hf
  · exact W.add_mem_iff_left (W.smul_mem (f v) hw)
  · constructor
    · intro hv
      have he : f v = 0 := by
        have := hf hv
        simpa [map_add, map_smul, hfw] using this
      simpa [he] using hv
    · intro hv
      have he : f v = 0 := hf hv
      simpa [he] using hv

/-- A nonzero proper invariant subspace of a full parabolic is its defining subspace. -/
theorem parabolic_le_imp_eq {W U : Submodule (ZMod 2) V}
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) (h : parabolic W ≤ parabolic U) : W = U := by
  have hWU : W ≤ U := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    intro w hw
    by_contra hwU
    have hus : u ∉ Submodule.span (ZMod 2) {w} := by
      rintro hs
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hs
      have ha0 : a ≠ 0 := by
        intro hz
        exact hu0 (by simpa [hz] using ha.symm)
      have huw : w = u := by simpa [scalar_one ha0] using ha
      exact hwU (huw.symm ▸ hu)
    obtain ⟨f, hfu, hf⟩ := (Submodule.span (ZMod 2) {w}).exists_le_ker_of_notMem hus
    have hfw : f w = 0 := hf (Submodule.mem_span_singleton_self w)
    have htu := (h (transvection_stabilizes hfw (Or.inl hw)) u).mpr hu
    change u + f u • w ∈ U at htu
    rw [scalar_one hfu, one_smul] at htu
    exact hwU ((U.add_mem_iff_right hu).mp htu)
  apply le_antisymm hWU
  intro u hu
  by_contra huW
  obtain ⟨f, hfu, hf⟩ := W.exists_le_ker_of_notMem huW
  have hfu1 := scalar_one hfu
  apply hU1
  apply top_unique
  intro x _
  let w := x - f x • u
  have hfw : f w = 0 := by simp [w, map_sub, map_smul, hfu1]
  have htu := (h (transvection_stabilizes hfw (Or.inr hf)) u).mpr hu
  change u + f u • w ∈ U at htu
  rw [hfu1, one_smul] at htu
  have hwU : w ∈ U := (U.add_mem_iff_right hu).mp htu
  have hx := U.add_mem hwU (U.smul_mem (f x) hu)
  simpa [w] using hx

theorem parabolic_ne_top {W : Submodule (ZMod 2) V} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) :
    parabolic W ≠ ⊤ := by
  intro ht
  exact hW0 (parabolic_le_imp_eq hW0 hW1 (W := ⊥) (by rw [ht]; exact le_top)).symm

theorem exists_linearEquiv_map_eq [FiniteDimensional (ZMod 2) V]
    (W U : Submodule (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U) :
    ∃ g : GL V, W.map g.toLinearMap = U := by
  obtain ⟨f⟩ := FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.mpr hd
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    change g w ∈ U
    rw [← hg ⟨w, hw⟩]
    exact (f ⟨w, hw⟩).property
  · intro u hu
    refine ⟨f.symm ⟨u, hu⟩, (f.symm ⟨u, hu⟩).property, ?_⟩
    simpa using (hg (f.symm ⟨u, hu⟩)).symm
end BinaryLinear.FourParabolicAction

end
