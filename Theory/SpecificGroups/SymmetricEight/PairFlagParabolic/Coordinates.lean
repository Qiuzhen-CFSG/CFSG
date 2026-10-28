module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Uses the ATLAS exceptional-isomorphism construction, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry
import all Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.Defs

/-!
# Coordinates for a simultaneous pair and four-block marking

The basis (e₀+e₁,e₁,e₂+e₃,e₃) has middle cut span(e₀,e₁).
The internal import of `FourBlockParabolic.Geometry` is used only to identify
the existing plane definition; its public boundary is preserved.

The first and third cuts are the line spanned by e₀+e₁ and the hyperplane
x₂=x₃. Their incident two-planes give the bivector pencil spanned by
(1,0,0,0,0,0) and (1,1,1,1,1,0).

A small kernel-checked calculation on two binary four-vectors identifies
membership in this pencil. All span and basis calculations are structural.
These coordinates supply the compatible A₃ markings in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 15.3.28(3) and 15.3.32(4),
printed pp.1131–1133.
-/

open Atlas.Order20160A8
open BinaryLinear.InvariantNodeActions
namespace Theory.SpecificGroups.SymmetricEight.PairFlagParabolic
@[expose] public noncomputable section
abbrev V := Fin 4 → ZMod 2
abbrev W := Fin 6 → ZMod 2

def lineVector : V := ![1,1,0,0]
def firstVector : W := ![1,0,0,0,0,0]
def secondVector : W := ![1,1,1,1,1,0]

def pencil : Submodule (ZMod 2) W where
  carrier := {w | w 1 = w 2 ∧ w 2 = w 3 ∧ w 3 = w 4 ∧ w 5 = 0}
  zero_mem' := by simp
  add_mem' hu hv := by
    exact ⟨congrArg₂ (· + ·) hu.1 hv.1,
      congrArg₂ (· + ·) hu.2.1 hv.2.1,
      congrArg₂ (· + ·) hu.2.2.1 hv.2.2.1, by simp only [Pi.add_apply, hu.2.2.2, hv.2.2.2, add_zero]⟩
  smul_mem' a w hw := by
    exact ⟨congrArg (a * ·) hw.1, congrArg (a * ·) hw.2.1,
      congrArg (a * ·) hw.2.2.1, by simp only [Pi.smul_apply, smul_eq_mul, hw.2.2.2, mul_zero]⟩

instance instDecidablePencil (w : W) : Decidable (w ∈ pencil) :=
  inferInstanceAs (Decidable (w 1 = w 2 ∧ w 2 = w 3 ∧ w 3 = w 4 ∧ w 5 = 0))

def hyperplane : Submodule (ZMod 2) V where
  carrier := {v | v 2 = v 3}
  zero_mem' := rfl
  add_mem' hu hv := congrArg₂ (· + ·) hu hv
  smul_mem' a _v hv := congrArg (a * ·) hv

instance instDecidableHyperplane (v : V) : Decidable (v ∈ hyperplane) :=
  inferInstanceAs (Decidable (v 2 = v 3))

theorem wedge_pencil_test : ∀ u v : V,
    Bivectors.wedge u v ∈ pencil ↔
      Bivectors.wedge u v = 0 ∨
        (u ∈ hyperplane ∧ v ∈ hyperplane ∧
          (u = lineVector ∨ v = lineVector ∨ u + v = lineVector)) := by
  decide +kernel

private theorem pencil_expansion (w : W) (hw : w ∈ pencil) :
    w = (w 0 - w 1) • firstVector + w 1 • secondVector := by
  ext i
  fin_cases i <;>
    simp [firstVector, secondVector, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]

theorem pencil_eq_span : pencil = Submodule.span (ZMod 2) {firstVector, secondVector} := by
  apply le_antisymm
  · intro w hw
    exact Submodule.mem_span_pair.mpr ⟨w 0 - w 1, w 1, (pencil_expansion w hw).symm⟩
  · apply Submodule.span_le.mpr
    rintro w (rfl | rfl) <;> simp [pencil, firstVector, secondVector]

private noncomputable def basisChange : V ≃ₗ[ZMod 2] V where
  toFun v := ![v 0, v 0 + v 1, v 2, v 2 + v 3]
  invFun v := ![v 0, v 1 - v 0, v 2, v 3 - v 2]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a v := by ext i; fin_cases i <;> simp [mul_add]

end
public noncomputable def basis : Basis 3 := (Pi.basisFun (ZMod 2) (Fin 4)).map basisChange

@[expose] public noncomputable section

theorem basis_apply (i : Fin 4) :
    basis i = (![lineVector, ![0,1,0,0], ![0,0,1,1], ![0,0,0,1]] : Fin 4 → V) i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [basis, basisChange, lineVector]

def line : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {lineVector}

theorem mem_line (v : V) : v ∈ line ↔ v = 0 ∨ v = lineVector := by
  rw [line, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha : a = 0 ∨ a = 1 := by revert a; decide
    rcases ha with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem cut_zero : cutSpace basis 0 = line := by
  change Submodule.span (ZMod 2) (basis '' {j : Fin 4 | j.val ≤ 0}) =
    Submodule.span (ZMod 2) {lineVector}
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have : j = 0 := Fin.ext (by simpa using hj)
    subst j
    exact basis_apply 0
  · rintro rfl
    exact ⟨0, by decide, basis_apply 0⟩

theorem cut_one : cutSpace basis 1 = FourBlockParabolic.plane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change i.val ≤ 1 at hi
    fin_cases i <;> simp_all [basis_apply, FourBlockParabolic.plane, lineVector]
  · intro v hv
    have he : v = v 0 • basis 0 + (v 1 - v 0) • basis 1 := by
      ext i
      fin_cases i <;> simp [basis_apply, lineVector, hv.1, hv.2]
    rw [he]
    apply Submodule.add_mem _ <;> apply Submodule.smul_mem _ <;>
      apply Submodule.subset_span
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

theorem cut_two : cutSpace basis 2 = hyperplane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change i.val ≤ 2 at hi
    fin_cases i <;> simp_all [basis_apply, hyperplane, lineVector]
  · intro v hv
    have he : v = v 0 • basis 0 + (v 1 - v 0) • basis 1 + v 2 • basis 2 := by
      ext i
      fin_cases i <;> simp [basis_apply, lineVector, show v 2 = v 3 from hv]
    rw [he]
    apply Submodule.add_mem _
    · apply Submodule.add_mem _ <;> apply Submodule.smul_mem _ <;>
        apply Submodule.subset_span
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
    · apply Submodule.smul_mem _
      exact Submodule.subset_span ⟨2, by decide, rfl⟩

theorem mem_parabolic_maps {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Finite U] (S : Submodule (ZMod 2) U) (g : BinaryLinear.GL U) :
    g ∈ BinaryLinear.parabolic S ↔ ∀ v ∈ S, g v ∈ S := by
  constructor
  · exact fun h v hv => (h v).mpr hv
  · intro h v
    refine ⟨?_, h v⟩
    intro hv
    let f : S → S := fun w => ⟨g w, h w w.property⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (g.injective (congrArg Subtype.val hxy))
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hf) ⟨g v, hv⟩
    exact (g.injective (congrArg Subtype.val hw)) ▸ w.property

end
end Theory.SpecificGroups.SymmetricEight.PairFlagParabolic
