module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density104.Witnesses
import Mathlib.Tactic.FinCases

/-!
# A checked rank-one operator in the degree-104 actor algebra

Every step of the block polynomial evaluation is a checked packed addition or
multiplication. The final value is the outer product of the two published seeds.
The generic straight-line checker then places that outer product in every
subalgebra containing the literal two actors.

A representative dense product took 14.4 seconds kernel time and 2.0 GB peak
RSS. The finite-check declarations run sequentially to bound simultaneous
kernel reduction; Lean's default thread setting is unchanged.
Source motivation: Guralnick–Malle Proposition 4.3; Aschbacher–Smith K.2, p.453.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density104Certificate
open Thompson.BinaryMatrix CycleCertificate

private theorem step_0 : Step 104 factorRows104 values operations 0 := by decide +kernel

private theorem step_1 : Step 104 factorRows104 values operations 1 := by rfl

private theorem step_2 : Step 104 factorRows104 values operations 2 := by rfl

private theorem step_3 : Step 104 factorRows104 values operations 3 := by decide +kernel

private theorem step_4 : Step 104 factorRows104 values operations 4 := by decide +kernel

private theorem step_5 : Step 104 factorRows104 values operations 5 := by decide +kernel

private theorem step_6 : Step 104 factorRows104 values operations 6 := by decide +kernel

private theorem step_7 : Step 104 factorRows104 values operations 7 := by decide +kernel

private theorem step_8 : Step 104 factorRows104 values operations 8 := by decide +kernel

private theorem step_9 : Step 104 factorRows104 values operations 9 := by decide +kernel

private theorem step_10 : Step 104 factorRows104 values operations 10 := by decide +kernel

private theorem step_11 : Step 104 factorRows104 values operations 11 := by decide +kernel

private theorem step_12 : Step 104 factorRows104 values operations 12 := by decide +kernel

private theorem step_13 : Step 104 factorRows104 values operations 13 := by decide +kernel

private theorem step_14 : Step 104 factorRows104 values operations 14 := by decide +kernel

private theorem step_15 : Step 104 factorRows104 values operations 15 := by decide +kernel

private theorem step_16 : Step 104 factorRows104 values operations 16 := by decide +kernel

private theorem step_17 : Step 104 factorRows104 values operations 17 := by decide +kernel

private theorem step_18 : Step 104 factorRows104 values operations 18 := by decide +kernel

private theorem step_19 : Step 104 factorRows104 values operations 19 := by decide +kernel

private theorem step_20 : Step 104 factorRows104 values operations 20 := by decide +kernel

private theorem step_21 : Step 104 factorRows104 values operations 21 := by decide +kernel

private theorem step_22 : Step 104 factorRows104 values operations 22 := by decide +kernel

private theorem step_23 : Step 104 factorRows104 values operations 23 := by decide +kernel

private theorem step_24 : Step 104 factorRows104 values operations 24 := by decide +kernel

private theorem step_25 : Step 104 factorRows104 values operations 25 := by decide +kernel

private theorem step_26 : Step 104 factorRows104 values operations 26 := by decide +kernel

private theorem step_27 : Step 104 factorRows104 values operations 27 := by decide +kernel

private theorem step_28 : Step 104 factorRows104 values operations 28 := by decide +kernel

private theorem step_29 : Step 104 factorRows104 values operations 29 := by decide +kernel

private theorem step_30 : Step 104 factorRows104 values operations 30 := by decide +kernel

private theorem step_31 : Step 104 factorRows104 values operations 31 := by decide +kernel

private theorem step_32 : Step 104 factorRows104 values operations 32 := by decide +kernel

private theorem step_33 : Step 104 factorRows104 values operations 33 := by decide +kernel

private theorem step_34 : Step 104 factorRows104 values operations 34 := by decide +kernel

private theorem step_35 : Step 104 factorRows104 values operations 35 := by decide +kernel

private theorem step_36 : Step 104 factorRows104 values operations 36 := by decide +kernel

private theorem step_37 : Step 104 factorRows104 values operations 37 := by decide +kernel

private theorem step_38 : Step 104 factorRows104 values operations 38 := by decide +kernel

private theorem step_39 : Step 104 factorRows104 values operations 39 := by decide +kernel

private theorem step_40 : Step 104 factorRows104 values operations 40 := by decide +kernel

private theorem step_41 : Step 104 factorRows104 values operations 41 := by decide +kernel

private theorem step_42 : Step 104 factorRows104 values operations 42 := by decide +kernel

private theorem step_43 : Step 104 factorRows104 values operations 43 := by decide +kernel

private theorem step_44 : Step 104 factorRows104 values operations 44 := by decide +kernel

private theorem step_45 : Step 104 factorRows104 values operations 45 := by decide +kernel

private theorem step_46 : Step 104 factorRows104 values operations 46 := by decide +kernel

private theorem step_47 : Step 104 factorRows104 values operations 47 := by decide +kernel

private theorem step_48 : Step 104 factorRows104 values operations 48 := by decide +kernel

private theorem step_49 : Step 104 factorRows104 values operations 49 := by decide +kernel

private theorem step_50 : Step 104 factorRows104 values operations 50 := by decide +kernel

private theorem step_51 : Step 104 factorRows104 values operations 51 := by decide +kernel

private theorem step_52 : Step 104 factorRows104 values operations 52 := by decide +kernel

private theorem step_53 : Step 104 factorRows104 values operations 53 := by decide +kernel

private theorem step_54 : Step 104 factorRows104 values operations 54 := by decide +kernel

private theorem step_55 : Step 104 factorRows104 values operations 55 := by decide +kernel

private theorem step_56 : Step 104 factorRows104 values operations 56 := by decide +kernel

private theorem steps : ∀ i : Fin 57, Step 104 factorRows104 values operations i.val := by
  intro i
  fin_cases i
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
  · exact step_9
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15
  · exact step_16
  · exact step_17
  · exact step_18
  · exact step_19
  · exact step_20
  · exact step_21
  · exact step_22
  · exact step_23
  · exact step_24
  · exact step_25
  · exact step_26
  · exact step_27
  · exact step_28
  · exact step_29
  · exact step_30
  · exact step_31
  · exact step_32
  · exact step_33
  · exact step_34
  · exact step_35
  · exact step_36
  · exact step_37
  · exact step_38
  · exact step_39
  · exact step_40
  · exact step_41
  · exact step_42
  · exact step_43
  · exact step_44
  · exact step_45
  · exact step_46
  · exact step_47
  · exact step_48
  · exact step_49
  · exact step_50
  · exact step_51
  · exact step_52
  · exact step_53
  · exact step_54
  · exact step_55
  · exact step_56

theorem value_mem
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 104) (Fin 104) (ZMod 2)))
    (h : ∀ a, factor104 a ∈ Q) (k : ℕ) (hk : k < 57) :
    decode 104 values[k]! ∈ Q :=
  certificate_mem 104 57 factorRows104 values operations steps Q h k hk

/-- The computed operator is the outer product of the two spanning seeds. -/
theorem rank_one : decode 104 values[56]! =
    Matrix.vecMulVec (fun i : Fin 104 => bit column i.val)
      (fun j : Fin 104 => bit row j.val) := by
  ext i j
  change bit (values[56]!)[i.val]! j.val = bit column i.val * bit row j.val
  revert i j
  decide +kernel

/-- A rank-one matrix in the algebra of the literal binary actors. -/
theorem rank_one_mem
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 104) (Fin 104) (ZMod 2)))
    (h : ∀ a, factor104 a ∈ Q) :
    Matrix.vecMulVec (fun i : Fin 104 => bit column i.val)
      (fun j : Fin 104 => bit row j.val) ∈ Q := by
  rw [← rank_one]
  exact value_mem Q h 56 (by decide)

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density104Certificate
