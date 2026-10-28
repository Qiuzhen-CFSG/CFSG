/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechForm.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCongruences
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The Leech bilinear form is the coordinate dot product scaled by one eighth.
Golay divisibility and the glue decomposition prove integrality and evenness.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def integerDot (x y : IntegerCoordinates) : ℤ := ∑ i, x i * y i

def rationalForm : LinearMap.BilinForm ℚ RationalCoordinates :=
  (1 / 8 : ℚ) • dotProductBilin ℚ ℚ

def rationalEmbedding : IntegerCoordinates →ₗ[ℤ] RationalCoordinates where
  toFun x := fun i => (x i : ℚ)
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

theorem rationalEmbedding_injective : Function.Injective rationalEmbedding := by
  intro x y h
  ext i
  have hi := congrFun h i
  change (x i : ℚ) = (y i : ℚ) at hi
  exact_mod_cast hi

theorem rationalForm_integer (x y : IntegerCoordinates) :
    rationalForm (rationalEmbedding x) (rationalEmbedding y) = (integerDot x y : ℚ) / 8 := by
  simp [rationalForm,dotProductBilin,rationalEmbedding,integerDot,dotProduct,div_eq_mul_inv]
  ring

theorem integerDot_comm (x y : IntegerCoordinates) : integerDot x y = integerDot y x := by
  simp [integerDot,mul_comm]

theorem integerDot_add_left (x y z : IntegerCoordinates) :
    integerDot (x+y) z = integerDot x z + integerDot y z := by
  simp [integerDot,add_mul,Finset.sum_add_distrib]

theorem integerDot_add_right (x y z : IntegerCoordinates) :
    integerDot x (y+z) = integerDot x y + integerDot x z := by
  simp [integerDot,mul_add,Finset.sum_add_distrib]

theorem integerDot_self_add (x y : IntegerCoordinates) :
    integerDot (x+y) (x+y) = integerDot x x + integerDot y y + 2 * integerDot x y := by
  rw [integerDot_add_left,integerDot_add_right,integerDot_add_right,integerDot_comm y x]
  ring

theorem integerDot_self_nonneg (x : IntegerCoordinates) : 0 ≤ integerDot x x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (x i)

theorem integerDot_self_zero (x : IntegerCoordinates) : integerDot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hle : x i * x i ≤ integerDot x x :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    rw [h] at hle
    have hn := mul_self_nonneg (x i)
    change x i = 0
    nlinarith
  · rintro rfl; simp [integerDot]

theorem integerDot_lift_self (c : BinaryWord) :
    integerDot (golayIntegerLift c) (golayIntegerLift c) = (hammingNorm c : ℤ) := by
  rw [← sum_golayIntegerLift]
  apply Finset.sum_congr rfl
  intro i _
  simp [golayIntegerLift]

theorem even_norm_divisible (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice) :
    16 ∣ integerDot x x := by
  obtain ⟨c,z,he⟩ := (evenGolayLattice_gluing x).mp hx
  have h : integerDot x x = 4 * (hammingNorm c.val : ℤ) +
      16 * ∑ i, (golayIntegerLift c.val i * z.val i + z.val i * z.val i) := by
    rw [← integerDot_lift_self]
    simp only [integerDot,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [he i]; ring
  obtain ⟨k,hk⟩ := golay_doublyEven c.val c.prop
  have hk' : (hammingNorm c.val : ℤ) = 4 * (k : ℤ) := by exact_mod_cast hk
  rw [h,hk']
  exact ⟨(k : ℤ) + ∑ i, (golayIntegerLift c.val i * z.val i + z.val i * z.val i),by ring⟩

theorem integerDot_oddGlue (a : Omega) (x : IntegerCoordinates) :
    integerDot x (oddGlue a) = (∑ i, x i) - 4 * x a := by
  simp [integerDot,oddGlue,mul_sub,Finset.sum_sub_distrib,mul_ite]
  ring

theorem oddGlue_norm (a : Omega) : integerDot (oddGlue a) (oddGlue a) = 32 := by
  rw [integerDot_oddGlue,oddGlue_sum]
  norm_num [oddGlue]

theorem even_dot_glue_divisible (a : Omega) (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice) :
    8 ∣ integerDot x (oddGlue a) := by
  rw [integerDot_oddGlue]
  have hs := ((even_congruences x).mp hx).2.2
  have hp := even_mem_coordinate_even x hx a
  apply Int.dvd_of_emod_eq_zero
  omega

theorem leech_norm_divisible (x : IntegerCoordinates) (hx : x ∈ leech) :
    16 ∣ integerDot x x := by
  change x ∈ leechAt ((0,0),0) at hx
  rcases hx with hx | hx
  · exact even_norm_divisible x hx
  · let a : Omega := ((0,0),0)
    have he : x = (x - oddGlue a) + oddGlue a := by abel
    rw [he,integerDot_self_add,oddGlue_norm]
    exact dvd_add (dvd_add (even_norm_divisible _ hx) (by norm_num))
      (by obtain ⟨k,hk⟩ := even_dot_glue_divisible a _ hx; exact ⟨k,by rw [hk]; ring⟩)

theorem leech_pairing_integral (x y : leech) :
    ∃ k : ℤ, rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) = k := by
  have hx := leech_norm_divisible x.val x.prop
  have hy := leech_norm_divisible y.val y.prop
  have hxy := leech_norm_divisible (x.val+y.val) (leech.add_mem x.prop y.prop)
  rw [integerDot_self_add] at hxy
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  obtain ⟨c,hc⟩ := hxy
  have h : integerDot x.val y.val = 8 * (c-a-b) := by omega
  refine ⟨c-a-b,?_⟩
  rw [rationalForm_integer,h]
  push_cast
  ring

theorem leech_norm_even (x : leech) :
    ∃ k : ℤ, rationalForm (rationalEmbedding x.val) (rationalEmbedding x.val) = 2 * k := by
  obtain ⟨k,hk⟩ := leech_norm_divisible x.val x.prop
  refine ⟨k,?_⟩
  rw [rationalForm_integer,hk]
  push_cast
  ring

end Atlas.Lattices
