module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.TraceWords

/-!
# The nonbinary trace witness

The certified fifteen-letter word has code trace 3, which evaluates
to t+1 in every field with t squared equal to t+1.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

open TraceWords

theorem trace_code : codeTrace Wababbababbabbab = FourteenData.traceCode := by decide +kernel

theorem trace_eq (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      FourteenData.traceWord).trace = coefficient t FourteenData.traceCode := by
  rw [FourteenData.traceWord, Wababbababbabbab_eval t ht, ← eval_trace, trace_code]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
