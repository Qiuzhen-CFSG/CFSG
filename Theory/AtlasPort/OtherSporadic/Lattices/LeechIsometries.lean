/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechIsometries.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechLattice
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
The group of all integral Leech isometries and its actions on norm shells.
Coordinate bounds make each shell finite; generation by minimal vectors makes the minimal-shell action faithful.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

/-- The full group of integer-linear lattice isometries, not a generated subgroup. -/
def leechIsometries : Subgroup (leech ≃ₗ[ℤ] leech) where
  carrier := {g | ∀ x y : leech, integerDot (g x).val (g y).val = integerDot x.val y.val}
  one_mem' := by
    change ∀ x y : leech, integerDot x.val y.val = integerDot x.val y.val
    intros; rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g.symm x) (g.symm y)
    simpa using h.symm

abbrev LeechIsometryGroup := ↥leechIsometries

theorem leechIsometry_preserves_form (g : LeechIsometryGroup) (x y : leech) :
    rationalForm (rationalEmbedding (g.val x).val) (rationalEmbedding (g.val y).val) =
      rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) := by
  rw [rationalForm_integer,rationalForm_integer,g.prop]

def LeechShell (r : ℤ) := {x : leech // integerDot x.val x.val = 8*r}

theorem shell_coordinate_bound (r : ℤ) (x : LeechShell r) (i : Omega) :
    -(8*r+1) ≤ x.val.val i ∧ x.val.val i ≤ 8*r+1 := by
  have hp := integerDot_self_nonneg x.val.val
  have hi : x.val.val i * x.val.val i ≤ integerDot x.val.val x.val.val :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (x.val.val j)) (Finset.mem_univ i)
  rw [x.prop] at hi hp
  constructor <;> nlinarith [sq_nonneg (x.val.val i - 1),sq_nonneg (x.val.val i + 1)]

instance shell_finite (r : ℤ) : Finite (LeechShell r) := by
  let f : LeechShell r → (Omega → {z : ℤ // z ∈ Finset.Icc (-(8*r+1)) (8*r+1)}) :=
    fun x i => ⟨x.val.val i,Finset.mem_Icc.mpr (shell_coordinate_bound r x i)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  ext i
  exact congrArg Subtype.val (congrFun h i)

def shellPermutation (g : LeechIsometryGroup) (r : ℤ) : Equiv.Perm (LeechShell r) where
  toFun x := ⟨g.val x.val,(g.prop _ _).trans x.prop⟩
  invFun x := ⟨g.val.symm x.val,((g⁻¹).prop _ _).trans x.prop⟩
  left_inv x := by apply Subtype.ext; exact g.val.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact g.val.apply_symm_apply x.val

def shellRepresentation (r : ℤ) : LeechIsometryGroup →* Equiv.Perm (LeechShell r) where
  toFun g := shellPermutation g r
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem minimal_shell_faithful : Function.Injective (shellRepresentation 4) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hs : ∀ z ∈ minimalSpan, ∀ hz : z ∈ leech,
      g.val ⟨z,hz⟩ = h.val ⟨z,hz⟩ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro hm
      have ht : integerDot z z = 8*4 := by simpa using hz.2
      have hh := Equiv.congr_fun he (⟨⟨z,hm⟩,ht⟩ : LeechShell 4)
      exact congrArg Subtype.val hh
    | zero =>
      intro hz
      change g.val 0 = h.val 0
      simp
    | add x y hx hy ihx ihy =>
      intro hz
      have hxm : x ∈ leech := minimalSpan_le hx
      have hym : y ∈ leech := minimalSpan_le hy
      change g.val ((⟨x,hxm⟩ : leech)+(⟨y,hym⟩ : leech)) =
        h.val ((⟨x,hxm⟩ : leech)+(⟨y,hym⟩ : leech))
      rw [map_add,map_add,ihx hxm,ihy hym]
    | smul r x hx ih =>
      intro hz
      have hxm : x ∈ leech := minimalSpan_le hx
      change g.val (r • (⟨x,hxm⟩ : leech)) = h.val (r • (⟨x,hxm⟩ : leech))
      rw [map_smul,map_smul,ih hxm]
  exact hs x.val (by rw [minimal_vectors_span]; exact x.prop) x.prop

instance leechIsometryGroup_finite : Finite LeechIsometryGroup :=
  Finite.of_injective (shellRepresentation 4) minimal_shell_faithful

end Atlas.Lattices
