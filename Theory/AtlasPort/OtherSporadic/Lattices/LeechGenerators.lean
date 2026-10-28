/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechGenerators.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechRank
public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis

/-!
The minimal vectors generate the integral Leech lattice.
Coordinate differences and Golay lifts generate the even part, and a glue vector supplies the odd coset.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def minimalSpan : Submodule ℤ IntegerCoordinates :=
  Submodule.span ℤ {x | x ∈ leech ∧ integerDot x x = 32}

theorem minimalSpan_le : minimalSpan ≤ leech :=
  Submodule.span_le.mpr (fun _ h => h.1)

theorem pair_norm (a b : Omega) (hab : a ≠ b) :
    integerDot (coordinateVector a 4 + coordinateVector b 4)
      (coordinateVector a 4 + coordinateVector b 4) = 32 := by
  rw [integerDot_self_add]
  simp only [integerDot_coordinateVector]
  simp [coordinateVector,Ne.symm hab]

theorem difference_mem (a b : Omega) : coordinateVector a 4 - coordinateVector b 4 ∈ leech := by
  have h := leech.sub_mem (coordinate_pair_mem a b) (coordinate_eight_mem b)
  convert h using 1
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,coordinateVector,Pi.single_apply]
  split_ifs <;> ring

theorem difference_norm (a b : Omega) (hab : a ≠ b) :
    integerDot (coordinateVector a 4 - coordinateVector b 4)
      (coordinateVector a 4 - coordinateVector b 4) = 32 := by
  unfold integerDot
  have h (i : Omega) :
      (coordinateVector a 4 - coordinateVector b 4) i *
        (coordinateVector a 4 - coordinateVector b 4) i =
      (if i = a then 16 else 0) + (if i = b then 16 else 0) := by
    simp only [Pi.sub_apply,coordinateVector,Pi.single_apply]
    split_ifs <;> simp_all
  simp_rw [h]
  simp [Finset.sum_add_distrib]

theorem difference_mem_minimalSpan (a b : Omega) :
    coordinateVector a 4 - coordinateVector b 4 ∈ minimalSpan := by
  by_cases h : a = b
  · subst b; simp only [sub_self]; exact minimalSpan.zero_mem
  · exact Submodule.subset_span ⟨difference_mem a b,difference_norm a b h⟩

theorem coordinate_eight_mem_minimalSpan (a : Omega) : coordinateVector a 8 ∈ minimalSpan := by
  obtain ⟨b,hab⟩ := exists_ne a
  have hp : coordinateVector a 4 + coordinateVector b 4 ∈ minimalSpan :=
    Submodule.subset_span ⟨coordinate_pair_mem a b,pair_norm a b (Ne.symm hab)⟩
  have hd := difference_mem_minimalSpan a b
  convert minimalSpan.add_mem hp hd using 1
  ext i
  simp only [Pi.add_apply,Pi.sub_apply,coordinateVector,Pi.single_apply]
  split_ifs <;> ring

theorem four_even_sum_mem_minimalSpan (z : IntegerCoordinates) (hz : z ∈ evenCoordinateSum) :
    (4 : ℤ) • z ∈ minimalSpan := by
  let a : Omega := ((0,0),0)
  have he : (4 : ℤ) • z =
      (∑ i, z i • (coordinateVector i 4 - coordinateVector a 4)) +
      ((∑ i, z i) / 2) • coordinateVector a 8 := by
    ext j
    have hs : (∑ i, z i) % 2 = 0 := hz
    simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Finset.sum_apply,Pi.sub_apply]
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    have hi : (∑ i, z i * coordinateVector i 4 j) = 4 * z j := by
      simp [coordinateVector,Pi.single_apply,mul_ite,mul_comm]
    rw [hi]
    by_cases hj : j = a
    · simp [coordinateVector,hj]
      omega
    · simp [coordinateVector,hj]
  rw [he]
  apply minimalSpan.add_mem
  · exact Submodule.sum_mem _ (fun i _ => minimalSpan.smul_mem _ (difference_mem_minimalSpan i a))
  · exact minimalSpan.smul_mem _ (coordinate_eight_mem_minimalSpan a)

def liftCarry (c d : BinaryWord) : IntegerCoordinates :=
  fun i => if c i ≠ 0 ∧ d i ≠ 0 then 1 else 0

theorem lift_add_carry (c d : BinaryWord) :
    golayIntegerLift c + golayIntegerLift d = golayIntegerLift (c+d) + 2 • liftCarry c d := by
  ext i
  rcases bit_cases (c i) with hc | hc <;> rcases bit_cases (d i) with hd | hd <;>
    simp [golayIntegerLift,liftCarry,Pi.add_apply,hc,hd]

theorem carry_even (c d : BinaryWord) (hc : c ∈ golay) (hd : d ∈ golay) :
    liftCarry c d ∈ evenCoordinateSum := by
  have ho := golay_selfOrthogonal hd c hc
  rw [binaryDot_overlap,ZMod.natCast_eq_zero_iff_even] at ho
  have hs : (∑ i, liftCarry c d i) = (overlap c d : ℤ) := by
    rw [overlap_eq_sum,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [liftCarry]
  change (∑ i, liftCarry c d i) % 2 = 0
  rw [hs]
  obtain ⟨k,hk⟩ := ho
  rw [hk]; push_cast; omega

def liftGeneratedCode : Submodule Bit BinaryWord where
  carrier := {c | c ∈ golay ∧ (2 : ℤ) • golayIntegerLift c ∈ minimalSpan}
  zero_mem' := ⟨golay.zero_mem,by
    have h : golayIntegerLift 0 = 0 := by ext i; simp [golayIntegerLift]
    rw [h,smul_zero]; exact minimalSpan.zero_mem⟩
  add_mem' := by
    rintro c d ⟨hc,hcl⟩ ⟨hd,hdl⟩
    refine ⟨golay.add_mem hc hd,?_⟩
    have he : (2 : ℤ) • golayIntegerLift (c+d) =
        (2 : ℤ) • golayIntegerLift c + (2 : ℤ) • golayIntegerLift d -
          (4 : ℤ) • liftCarry c d := by
      ext i
      have h := congrFun (lift_add_carry c d) i
      change golayIntegerLift c i + golayIntegerLift d i =
        golayIntegerLift (c+d) i + 2 * liftCarry c d i at h
      change 2 * golayIntegerLift (c+d) i =
        2 * golayIntegerLift c i + 2 * golayIntegerLift d i - 4 * liftCarry c d i
      omega
    rw [he]
    exact minimalSpan.sub_mem (minimalSpan.add_mem hcl hdl)
      (four_even_sum_mem_minimalSpan _ (carry_even c d hc hd))
  smul_mem' := by
    intro r c hc
    rcases bit_cases r with hr | hr
    · subst r
      rw [zero_smul]
      refine ⟨golay.zero_mem,?_⟩
      have h : golayIntegerLift 0 = 0 := by ext i; simp [golayIntegerLift]
      rw [h,smul_zero]; exact minimalSpan.zero_mem
    · subst r; simpa using hc

theorem code_lift_mem_minimalSpan (c : BinaryWord) (hc : c ∈ golay) :
    (2 : ℤ) • golayIntegerLift c ∈ minimalSpan := by
  have h : golay ≤ liftGeneratedCode := by
    rw [← octads_span]
    apply Submodule.span_le.mpr
    rintro c ⟨hc,hw⟩
    refine ⟨hc,Submodule.subset_span ⟨?_,?_⟩⟩
    · apply Or.inl
      exact ⟨golayIntegerLift c,lift_mem_evenHalfLattice c hc,rfl⟩
    · have he : integerDot ((2 : ℤ) • golayIntegerLift c) ((2 : ℤ) • golayIntegerLift c) =
          4 * integerDot (golayIntegerLift c) (golayIntegerLift c) := by
        simp only [integerDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _; ring
      rw [he,integerDot_lift_self,hw]; norm_num
  exact (h hc).2

theorem minimal_vectors_span : minimalSpan = leech := by
  apply le_antisymm minimalSpan_le
  intro x hx
  have he (e : IntegerCoordinates) (he : e ∈ evenGolayLattice) : e ∈ minimalSpan := by
    obtain ⟨c,z,hz⟩ := (evenGolayLattice_gluing e).mp he
    have hv : e = (2 : ℤ) • golayIntegerLift c.val + (4 : ℤ) • z.val := by
      ext i; exact hz i
    rw [hv]
    exact minimalSpan.add_mem (code_lift_mem_minimalSpan c.val c.prop)
      (four_even_sum_mem_minimalSpan z.val z.prop)
  change x ∈ leechAt ((0,0),0) at hx
  rcases hx with hx | hx
  · exact he x hx
  · have hu : oddGlue ((0,0),0) ∈ minimalSpan :=
      Submodule.subset_span ⟨oddGlue_mem _,oddGlue_norm _⟩
    convert minimalSpan.add_mem (he _ hx) hu using 1; abel

end Atlas.Lattices
