module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Uses the ATLAS exceptional-isomorphism construction, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.Coordinates

/-!
# The bivector pencil and its middle-node parabolic

Two distinct planes in the pencil intersect in the line spanned by e₀+e₁
and generate the three-space x₂=x₃. Naturality of the exterior square
therefore identifies the pencil stabilizer with the simultaneous stabilizer
of these two cuts: the middle-node minimal parabolic for the marked basis.

Only the two-vector coordinate lemma from `Coordinates` is used as a finite
certificate. Injectivity of the linear action reconstructs the common line;
linearity extends the two generator calculations to the whole pencil.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.28(3), printed p.1131, via the ATLAS exterior-square comparison.
-/

open Atlas.Order20160A8
open BinaryLinear.InvariantNodeActions
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.PairFlagParabolic
noncomputable section

theorem pencil_eq_wedge_span : pencil = Submodule.span (ZMod 2)
    {Bivectors.wedge (basis 0) (basis 1), Bivectors.wedge (basis 0) (basis 2)} := by
  apply le_antisymm
  · intro w hw
    apply Submodule.mem_span_pair.mpr
    refine ⟨w 0, w 1, ?_⟩
    ext i
    fin_cases i <;>
      simp [basis_apply, Bivectors.wedge, lineVector, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]
  · apply Submodule.span_le.mpr
    rintro w (rfl | rfl) <;> simp [basis_apply, Bivectors.wedge, lineVector, pencil]

theorem mem_minimalParabolic (g : BinaryLinear.GL V) :
    g ∈ minimalParabolic basis 1 ↔
      g ∈ BinaryLinear.parabolic line ∧ g ∈ BinaryLinear.parabolic hyperplane := by
  change g ∈ cutStabilizer basis {1}ᶜ ↔ _
  simp only [cutStabilizer, Subgroup.mem_iInf]
  constructor
  · intro h
    exact ⟨cut_zero ▸ h 0 (by decide), cut_two ▸ h 2 (by decide)⟩
  · rintro ⟨h0, h2⟩ i hi
    fin_cases i
    · change g ∈ BinaryLinear.parabolic (cutSpace basis 0)
      rw [cut_zero]
      exact h0
    · exact False.elim (hi rfl)
    · change g ∈ BinaryLinear.parabolic (cutSpace basis 2)
      rw [cut_two]
      exact h2

theorem mem_parabolic_line (g : BinaryLinear.GL V) :
    g ∈ BinaryLinear.parabolic line ↔ g lineVector = lineVector := by
  rw [mem_parabolic_maps]
  constructor
  · intro h
    rcases (mem_line _).mp (h lineVector ((mem_line _).mpr (Or.inr rfl))) with hz | he
    · exact False.elim ((by decide : lineVector ≠ 0) (g.map_eq_zero_iff.mp hz))
    · exact he
  · intro h v hv
    rcases (mem_line _).mp hv with rfl | rfl
    · exact (mem_line _).mpr (Or.inl g.map_zero)
    · exact (mem_line _).mpr (Or.inr h)

theorem mem_parabolic_hyperplane (g : BinaryLinear.GL V) :
    g ∈ BinaryLinear.parabolic hyperplane ↔
      g (basis 0) ∈ hyperplane ∧ g (basis 1) ∈ hyperplane ∧ g (basis 2) ∈ hyperplane := by
  rw [mem_parabolic_maps, ← cut_two]
  constructor
  · intro h
    exact ⟨h _ (Submodule.subset_span ⟨0, by decide, rfl⟩),
      h _ (Submodule.subset_span ⟨1, by decide, rfl⟩),
      h _ (Submodule.subset_span ⟨2, by decide, rfl⟩)⟩
  · rintro ⟨h0, h1, h2⟩
    change cutSpace basis 2 ≤ (cutSpace basis 2).comap g.toLinearMap
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change i.val ≤ 2 at hi
    change g (basis i) ∈ cutSpace basis 2
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · norm_num at hi

theorem common_line (g : BinaryLinear.GL V)
    (h1 : g (basis 0) = lineVector ∨ g (basis 1) = lineVector ∨
      g (basis 0) + g (basis 1) = lineVector)
    (h2 : g (basis 0) = lineVector ∨ g (basis 2) = lineVector ∨
      g (basis 0) + g (basis 2) = lineVector) :
    g (basis 0) = lineVector := by
  have hne : g (basis 1) ≠ g (basis 2) := fun h =>
    (by simp [basis_apply] : basis 1 ≠ basis 2) (g.injective h)
  have hn012 : g (basis 0) + g (basis 1) ≠ g (basis 2) := by
    intro h
    have hh := g.injective ((g.map_add _ _).trans h)
    have : basis 0 + basis 1 ≠ basis 2 := by rw [basis_apply, basis_apply, basis_apply]; decide
    exact this hh
  have hn021 : g (basis 0) + g (basis 2) ≠ g (basis 1) := by
    intro h
    have hh := g.injective ((g.map_add _ _).trans h)
    have : basis 0 + basis 2 ≠ basis 1 := by rw [basis_apply, basis_apply, basis_apply]; decide
    exact this hh
  rcases h1 with h | h | h
  · exact h
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact False.elim (hne (h.trans h2.symm))
    · exact False.elim (hn021 (h2.trans h.symm))
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact False.elim (hn012 (h.trans h2.symm))
    · exact False.elim (hne (add_left_cancel (h.trans h2.symm)))

public theorem exterior_parabolic_iff (s : SL(4, ZMod 2)) :
    Exterior.exteriorAction s ∈ BinaryLinear.parabolic pencil ↔
      BinaryLinear.OuterCyclic.slEquivLinear 4 s ∈ minimalParabolic basis 1 := by
  let g := BinaryLinear.OuterCyclic.slEquivLinear 4 s
  have natural (u v : V) : Exterior.exteriorAction s (Bivectors.wedge u v) =
      Bivectors.wedge (g u) (g v) := Bivectors.exteriorMap_wedge s.val u v
  have hx1 : Bivectors.wedge (basis 0) (basis 1) ∈ pencil := by
    simp [basis_apply, Bivectors.wedge, lineVector, pencil]
  have hx2 : Bivectors.wedge (basis 0) (basis 2) ∈ pencil := by
    simp [basis_apply, Bivectors.wedge, lineVector, pencil]
  have hn1 : Bivectors.wedge (g (basis 0)) (g (basis 1)) ≠ 0 := by
    rw [← natural]
    intro h
    have hh := (Exterior.exteriorAction s).map_eq_zero_iff.mp h
    have : Bivectors.wedge (basis 0) (basis 1) ≠ 0 := by
      rw [basis_apply, basis_apply]; decide
    exact this hh
  have hn2 : Bivectors.wedge (g (basis 0)) (g (basis 2)) ≠ 0 := by
    rw [← natural]
    intro h
    have hh := (Exterior.exteriorAction s).map_eq_zero_iff.mp h
    have : Bivectors.wedge (basis 0) (basis 2) ≠ 0 := by
      rw [basis_apply, basis_apply]; decide
    exact this hh
  rw [mem_minimalParabolic]
  constructor
  · intro h
    have hm1 : Bivectors.wedge (g (basis 0)) (g (basis 1)) ∈ pencil := by
      rw [← natural]
      exact (h _).mpr hx1
    have hm2 : Bivectors.wedge (g (basis 0)) (g (basis 2)) ∈ pencil := by
      rw [← natural]
      exact (h _).mpr hx2
    have hh1 := (wedge_pencil_test _ _).mp hm1
    have hh2 := (wedge_pencil_test _ _).mp hm2
    have a := hh1.resolve_left hn1
    have b := hh2.resolve_left hn2
    refine ⟨(mem_parabolic_line g).mpr ?_, (mem_parabolic_hyperplane g).mpr ⟨a.1, a.2.1, b.2.1⟩⟩
    simpa only [basis_apply, Matrix.cons_val_zero] using common_line g a.2.2 b.2.2
  · rintro ⟨hl, hh⟩
    have hfix : g (basis 0) = lineVector := by
      simpa only [basis_apply, Matrix.cons_val_zero] using (mem_parabolic_line g).mp hl
    have hh := (mem_parabolic_hyperplane g).mp hh
    rw [mem_parabolic_maps]
    change pencil ≤ pencil.comap (Exterior.exteriorAction s).toLinearMap
    nth_rw 1 [pencil_eq_wedge_span]
    apply Submodule.span_le.mpr
    rintro w (rfl | rfl)
    · change Exterior.exteriorAction s (Bivectors.wedge (basis 0) (basis 1)) ∈ pencil
      rw [natural, wedge_pencil_test]
      exact Or.inr ⟨hh.1, hh.2.1, Or.inl hfix⟩
    · change Exterior.exteriorAction s (Bivectors.wedge (basis 0) (basis 2)) ∈ pencil
      rw [natural, wedge_pencil_test]
      exact Or.inr ⟨hh.1, hh.2.2, Or.inl hfix⟩

end
end Theory.SpecificGroups.SymmetricEight.PairFlagParabolic
