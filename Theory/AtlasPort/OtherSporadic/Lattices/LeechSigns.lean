/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechIsometries

/-!
Golay sign changes as explicit Leech isometries.
Code orthogonality preserves the lattice congruences, and coordinatewise signs preserve the dot product.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def signChange (c : BinaryWord) : IntegerCoordinates →ₗ[ℤ] IntegerCoordinates where
  toFun x := fun i => if c i = 0 then x i else -x i
  map_add' x y := by ext i; by_cases h : c i = 0 <;> simp [h,add_comm]
  map_smul' r x := by ext i; by_cases h : c i = 0 <;> simp [h]

theorem signChange_involutive (c : BinaryWord) (x : IntegerCoordinates) :
    signChange c (signChange c x) = x := by
  ext i
  by_cases h : c i = 0 <;> simp [signChange,h]

theorem signChange_add (c d : BinaryWord) (x : IntegerCoordinates) :
    signChange (c+d) x = signChange c (signChange d x) := by
  ext i
  rcases bit_cases (c i) with hc | hc <;> rcases bit_cases (d i) with hd | hd <;>
    simp [signChange,Pi.add_apply,hc,hd]

theorem signChange_dot (c : BinaryWord) (x y : IntegerCoordinates) :
    integerDot (signChange c x) (signChange c y) = integerDot x y := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = 0 <;> simp [signChange,h]

theorem signChange_sum (c : BinaryWord) (x : IntegerCoordinates) :
    (∑ i, signChange c x i) = (∑ i, x i) - 2 * integerDot x (golayIntegerLift c) := by
  simp only [integerDot,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = 0 <;> simp [signChange,golayIntegerLift,h] ; ring

theorem code_pairing_divisible (c : BinaryWord) (hc : c ∈ golay)
    (x : IntegerCoordinates) (hx : x ∈ leech) : 4 ∣ integerDot x (golayIntegerLift c) := by
  have hl : (2 : ℤ) • golayIntegerLift c ∈ leech := by
    exact Or.inl ⟨golayIntegerLift c,lift_mem_evenHalfLattice c hc,rfl⟩
  have hd := integer_dual_divisible x
    (rationalLeech_le_dual (Submodule.mem_map.mpr ⟨x,hx,rfl⟩)) _ hl
  have he : integerDot x ((2 : ℤ) • golayIntegerLift c) = 2 * integerDot x (golayIntegerLift c) := by
    simp only [integerDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [he] at hd
  obtain ⟨k,hk⟩ := hd
  exact ⟨k,by omega⟩

theorem signChange_even_residue (c : BinaryWord) (x : IntegerCoordinates)
    (hp : ∀ i, x i % 2 = 0) : halfResidue (signChange c x) 0 = halfResidue x 0 := by
  ext i
  by_cases h : c i = 0
  · simp [halfResidue,integerReduction,signChange,h]
  · have he : signChange c x i = -x i := by simp [signChange,h]
    change (((signChange c x i - 0) / 2 : ℤ) : Bit) = (((x i - 0) / 2 : ℤ) : Bit)
    rw [he]
    apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
    have h := hp i
    omega

theorem signChange_odd_residue (c : BinaryWord) (x : IntegerCoordinates)
    (hp : ∀ i, x i % 2 = 1) : halfResidue (signChange c x) 1 = halfResidue x 1 + c := by
  ext i
  rcases bit_cases (c i) with h | h
  · simp [halfResidue,integerReduction,signChange,h]
  · change (((signChange c x i - 1) / 2 : ℤ) : Bit) = (((x i - 1) / 2 : ℤ) : Bit) + c i
    have he : signChange c x i = -x i := by simp [signChange,h]
    rw [he,h]
    have hq : (((-x i - 1) / 2 : ℤ) : Bit) = (((x i - 1) / 2 + 1 : ℤ) : Bit) := by
      apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
      have h := hp i
      omega
    simpa only [Int.cast_add,Int.cast_one] using hq

theorem signChange_preserves (c : BinaryWord) (hc : c ∈ golay)
    (x : IntegerCoordinates) (hx : x ∈ leech) : signChange c x ∈ leech := by
  obtain ⟨m,(hm | hm),hp,hr,hs⟩ := (mem_leech x).mp hx
  · subst m
    apply (mem_leech _).mpr
    refine ⟨0,Or.inl rfl,fun i => ?_,?_,?_⟩
    · have h := hp i
      by_cases hi : c i = 0 <;> simp only [signChange,LinearMap.coe_mk,AddHom.coe_mk,hi,ite_true,ite_false] <;> omega
    · rw [signChange_even_residue c x hp]; exact hr
    · rw [signChange_sum]
      obtain ⟨k,hk⟩ := code_pairing_divisible c hc x hx
      rw [hk]; omega
  · subst m
    apply (mem_leech _).mpr
    refine ⟨1,Or.inr rfl,fun i => ?_,?_,?_⟩
    · have h := hp i
      by_cases hi : c i = 0 <;> simp only [signChange,LinearMap.coe_mk,AddHom.coe_mk,hi,ite_true,ite_false] <;> omega
    · rw [signChange_odd_residue c x hp]; exact golay.add_mem hr hc
    · rw [signChange_sum]
      obtain ⟨k,hk⟩ := code_pairing_divisible c hc x hx
      rw [hk]; omega

def signIsometry (c : golay) : LeechIsometryGroup :=
  ⟨{ toFun := fun x => ⟨signChange c.val x.val,signChange_preserves c.val c.prop x.val x.prop⟩
     invFun := fun x => ⟨signChange c.val x.val,signChange_preserves c.val c.prop x.val x.prop⟩
     left_inv := fun x => Subtype.ext (signChange_involutive c.val x.val)
     right_inv := fun x => Subtype.ext (signChange_involutive c.val x.val)
     map_add' := fun x y => Subtype.ext ((signChange c.val).map_add x.val y.val)
     map_smul' := fun r x => Subtype.ext ((signChange c.val).map_smul r x.val) },
    fun x y => signChange_dot c.val x.val y.val⟩

end Atlas.Lattices
