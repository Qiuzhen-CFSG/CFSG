module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.FiniteConditions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit.Certificates0
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit.Certificates1
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit.Certificates2
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit.Certificates3
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit.Certificates4
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit.Certificates5

/-!
# Closure of the J₁ involution matrix family

The kernel-checked certificates identify each packed matrix with the published
`orbitMatrix` and prove `A * Xᵢ = Xⱼ * A` and `B * Xᵢ = Xₖ * B`, using the
zero-based transition targets from `Source/data.json`. The generator orders
turn these intertwining identities into the two conjugation identities.
The result has no additional premises.

This is the finite orbit-closure input to `Reduction.involution_mem_orbit`,
supporting the `Out(J₁) = 1` entry of GLS3, Table 5.3f. The independent
generator-image calculation and outer-theorem assembly remain with their
respective owners. The actual ATLAS matrices and generator orders are in
`Theory.SpecificGroups.Janko1.Model.Basic`.
-/

namespace Janko1.OuterCertificate

open InvolutionOrbit

private theorem certified (i : Fin 1463) : Certified i := by
  refine forall_of_blocks Certified ?_ i
  intro b r
  fin_cases b
  · exact certificateBlock0 r
  · exact certificateBlock1 r
  · exact certificateBlock2 r
  · exact certificateBlock3 r
  · exact certificateBlock4 r
  · exact certificateBlock5 r
  · exact certificateBlock6 r
  · exact certificateBlock7 r
  · exact certificateBlock8 r
  · exact certificateBlock9 r
  · exact certificateBlock10 r
  · exact certificateBlock11 r
  · exact certificateBlock12 r
  · exact certificateBlock13 r
  · exact certificateBlock14 r
  · exact certificateBlock15 r
  · exact certificateBlock16 r
  · exact certificateBlock17 r
  · exact certificateBlock18 r
  · exact certificateBlock19 r
  · exact certificateBlock20 r
  · exact certificateBlock21 r
  · exact certificateBlock22 r
  · exact certificateBlock23 r
  · exact certificateBlock24 r
  · exact certificateBlock25 r
  · exact certificateBlock26 r
  · exact certificateBlock27 r
  · exact certificateBlock28 r
  · exact certificateBlock29 r
  · exact certificateBlock30 r
  · exact certificateBlock31 r
  · exact certificateBlock32 r
  · exact certificateBlock33 r
  · exact certificateBlock34 r
  · exact certificateBlock35 r
  · exact certificateBlock36 r
  · exact certificateBlock37 r
  · exact certificateBlock38 r
  · exact certificateBlock39 r
  · exact certificateBlock40 r
  · exact certificateBlock41 r
  · exact certificateBlock42 r
  · exact certificateBlock43 r
  · exact certificateBlock44 r
  · exact certificateBlock45 r

private theorem decode_code (i : Fin 1463) : decode (code i) = orbitMatrix i :=
  (certified i).1

private theorem matrixA_square : matrixA * matrixA = 1 := by
  have h := congrArg OrderCertificate.matrixValue a_pow_two
  rw [map_pow, map_one] at h
  change matrixA ^ 2 = 1 at h
  simpa only [pow_two] using h

private theorem matrixB_cube : matrixB * (matrixB * matrixB) = 1 := by
  have h := congrArg OrderCertificate.matrixValue b_pow_three
  rw [map_pow, map_one] at h
  change matrixB ^ 3 = 1 at h
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

/-- The published family is closed under conjugation by both standard generators. -/
public theorem orbitClosed : OrbitClosed := by
  constructor
  · intro i
    refine ⟨targetA i, ?_⟩
    have h : matrixA * orbitMatrix i = orbitMatrix (targetA i) * matrixA := by
      simpa only [decode_generatorA, decode_code] using
        check_sound generatorA (code i) (code (targetA i)) generatorA (certified i).2.1
    rw [h, mul_assoc, matrixA_square, mul_one]
  · intro i
    refine ⟨targetB i, ?_⟩
    have h : matrixB * orbitMatrix i = orbitMatrix (targetB i) * matrixB := by
      simpa only [decode_generatorB, decode_code] using
        check_sound generatorB (code i) (code (targetB i)) generatorB (certified i).2.2
    rw [h, mul_assoc, matrixB_cube, mul_one]

end Janko1.OuterCertificate
