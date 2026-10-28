/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechDual.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCoordinates

/-!
Self-duality of the embedded rational Leech lattice.
Pairing with coordinate vectors forces integral coordinates; Golay orthogonality recovers the lattice congruences.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

theorem rationalForm_coordinate_eight (x : RationalCoordinates) (a : Omega) :
    rationalForm x (rationalEmbedding (coordinateVector a 8)) = x a := by
  simp [rationalForm,dotProductBilin,rationalEmbedding,coordinateVector,Pi.single_apply,
    dotProduct,mul_ite]
  ring

theorem dual_integer_coordinates (w : RationalCoordinates) (hw : w ∈ leechDual) :
    ∃ x : IntegerCoordinates, rationalEmbedding x = w := by
  have hi (a : Omega) : ∃ k : ℤ, (k : ℚ) = w a := by
    have h := hw _ (Submodule.mem_map.mpr ⟨coordinateVector a 8,coordinate_eight_mem a,rfl⟩)
    rw [rationalForm_coordinate_eight] at h
    exact Submodule.mem_one.mp h
  choose x hx using hi
  exact ⟨x,funext hx⟩

theorem integer_dual_divisible (x : IntegerCoordinates) (hx : rationalEmbedding x ∈ leechDual)
    (y : IntegerCoordinates) (hy : y ∈ leech) : 8 ∣ integerDot x y := by
  obtain ⟨k,hk⟩ := Submodule.mem_one.mp (hx _ (Submodule.mem_map.mpr ⟨y,hy,rfl⟩))
  rw [rationalForm_integer] at hk
  refine ⟨k,?_⟩
  have hq : (integerDot x y : ℚ) = 8 * (k : ℚ) := by
    change (k : ℚ) = (integerDot x y : ℚ) / 8 at hk
    linarith
  exact_mod_cast hq

theorem reduction_lift_dot (y : IntegerCoordinates) (c : BinaryWord) :
    ((integerDot y (golayIntegerLift c) : ℤ) : Bit) = binaryDot (integerReduction y) c := by
  simp only [integerDot,Int.cast_sum,Int.cast_mul,binaryDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrFun (integerReduction_lift c) i
  change (y i : Bit) * (golayIntegerLift c i : Bit) = (y i : Bit) * c i
  rw [show (golayIntegerLift c i : Bit) = c i from h]

theorem integer_dual_congruences (x : IntegerCoordinates)
    (hx : rationalEmbedding x ∈ leechDual) : LeechCongruences x := by
  let a : Omega := ((0,0),0)
  let m : ℤ := x a % 2
  have hm : m = 0 ∨ m = 1 := by dsimp [m]; omega
  have hp (i : Omega) : x i % 2 = m := by
    have h := integer_dual_divisible x hx _ (coordinate_pair_mem i a)
    rw [integerDot_add_right,integerDot_coordinateVector,integerDot_coordinateVector] at h
    obtain ⟨k,hk⟩ := h
    dsimp [m]; omega
  let y : IntegerCoordinates := fun i => (x i - m) / 2
  have he (i : Omega) : x i = m + 2 * y i := by
    have h := hp i
    dsimp [y]
    rcases hm with hm | hm <;> omega
  have hc : integerReduction y ∈ golay := by
    rw [golay_selfDual]
    intro c hc
    have hl : (fun i => 2 * golayIntegerLift c i) ∈ leech := by
      apply Or.inl
      apply (mem_evenGolayLattice _).mpr
      exact ⟨golayIntegerLift c,(lift_mem_evenHalfLattice c hc).1,
        (lift_mem_evenHalfLattice c hc).2,fun i => rfl⟩
    have hd := integer_dual_divisible x hx _ hl
    have hdot : integerDot x (fun i => 2 * golayIntegerLift c i) =
        2 * m * (hammingNorm c : ℤ) + 4 * integerDot y (golayIntegerLift c) := by
      rw [← sum_golayIntegerLift]
      simp only [integerDot,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [he i]; ring
    obtain ⟨k,hk⟩ := golay_doublyEven c hc
    have hk' : (hammingNorm c : ℤ) = 4 * (k : ℤ) := by exact_mod_cast hk
    rw [hdot,hk'] at hd
    obtain ⟨r,hr⟩ := hd
    have h2 : 2 ∣ integerDot y (golayIntegerLift c) := by
      refine ⟨r - m*k,?_⟩
      nlinarith [hr]
    have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h2
    rw [reduction_lift_dot] at hb
    rw [binaryDot_symmetric]
    exact hb
  refine ⟨m,hm,hp,hc,?_⟩
  have hs := integer_dual_divisible x hx (oddGlue a) (oddGlue_mem a)
  rw [integerDot_oddGlue] at hs
  obtain ⟨k,hk⟩ := hs
  have hpa := hp a
  rcases hm with hm | hm <;> omega

theorem leech_selfDual : leechDual = rationalLeech := by
  apply le_antisymm
  · intro w hw
    obtain ⟨x,rfl⟩ := dual_integer_coordinates w hw
    exact Submodule.mem_map.mpr ⟨x,(mem_leech x).mpr (integer_dual_congruences x hw),rfl⟩
  · exact rationalLeech_le_dual

end Atlas.Lattices
