/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechGeneratorCriterion.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGenerators

/-!
A finite criterion for a submodule to contain the Leech lattice.
Coordinate differences, one axis vector, the twelve Golay generator lifts, and one odd glue vector suffice.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

/-- A finite generating criterion retaining the Golay lift and gluing construction. -/
theorem leech_le_of_generators (P : Submodule ℤ IntegerCoordinates) (a : Omega)
    (hd : ∀ i, coordinateVector i 4 - coordinateVector a 4 ∈ P)
    (h8 : coordinateVector a 8 ∈ P)
    (hc : ∀ i : Fin 12, (2 : ℤ) • golayIntegerLift (golayGenerators i) ∈ P)
    (hu : oddGlue a ∈ P) : leech ≤ P := by
  have hfour (z : IntegerCoordinates) (hz : z ∈ evenCoordinateSum) : (4 : ℤ) • z ∈ P := by
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
      · simp [coordinateVector,hj]; omega
      · simp [coordinateVector,hj]
    rw [he]
    exact P.add_mem (P.sum_mem (fun i _ => P.smul_mem _ (hd i))) (P.smul_mem _ h8)
  let D : Submodule Bit BinaryWord := {
    carrier := {c | c ∈ golay ∧ (2 : ℤ) • golayIntegerLift c ∈ P}
    zero_mem' := ⟨golay.zero_mem,by
      have he : golayIntegerLift 0 = 0 := by ext i; simp [golayIntegerLift]
      rw [he,smul_zero]; exact P.zero_mem⟩
    add_mem' := by
      rintro c d ⟨hcg,hcp⟩ ⟨hdg,hdp⟩
      refine ⟨golay.add_mem hcg hdg,?_⟩
      have he : (2 : ℤ) • golayIntegerLift (c+d) =
          (2 : ℤ) • golayIntegerLift c + (2 : ℤ) • golayIntegerLift d -
          (4 : ℤ) • liftCarry c d := by
        ext i
        have hh := congrFun (lift_add_carry c d) i
        change golayIntegerLift c i + golayIntegerLift d i =
          golayIntegerLift (c+d) i + 2 * liftCarry c d i at hh
        change 2 * golayIntegerLift (c+d) i =
          2 * golayIntegerLift c i + 2 * golayIntegerLift d i - 4 * liftCarry c d i
        omega
      rw [he]
      exact P.sub_mem (P.add_mem hcp hdp) (hfour _ (carry_even c d hcg hdg))
    smul_mem' := by
      intro r c h
      rcases bit_cases r with hr | hr
      · subst r; rw [zero_smul]
        refine ⟨golay.zero_mem,?_⟩
        have he : golayIntegerLift 0 = 0 := by ext i; simp [golayIntegerLift]
        rw [he,smul_zero]; exact P.zero_mem
      · subst r; simpa using h }
  have hlift (c : golay) : (2 : ℤ) • golayIntegerLift c.val ∈ P := by
    have hs := congrArg Subtype.val (golayBasis.sum_repr c)
    change (∑ i, golayBasis.repr c i • (golayBasis i).val) = c.val at hs
    have hD : c.val ∈ D := by
      rw [← hs]
      apply D.sum_mem
      intro i _
      apply D.smul_mem
      exact ⟨(golayBasis i).prop,by rw [golayBasis_coe]; exact hc i⟩
    exact hD.2
  have heven (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice) : x ∈ P := by
    obtain ⟨c,z,hz⟩ := (evenGolayLattice_gluing x).mp hx
    have he : x = (2 : ℤ) • golayIntegerLift c.val + (4 : ℤ) • z.val := by
      ext i; exact hz i
    rw [he]
    exact P.add_mem (hlift c) (hfour z.val z.prop)
  intro x hx
  have hx' : x ∈ leechAt a := by
    change x ∈ leechAt ((0,0),0) at hx
    rwa [leechAt_independent ((0,0),0) a] at hx
  rcases hx' with hx' | hx'
  · exact heven x hx'
  · convert P.add_mem (heven _ hx') hu using 1; abel

end Atlas.Lattices
