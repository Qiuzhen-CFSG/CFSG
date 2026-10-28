module
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.Diagram

/-!
# Diagram triviality under arbitrary PSL₃(4) markings

Choose an entrywise field isomorphism and compare it with the given abstract
isomorphism. The discrepancy is an automorphism of the target. The geometric
diagram kernel is normal, so conjugating by this discrepancy preserves it.
The field transport theorem then returns to the original parabolic classes.

This permits independently selected quotient and representation markings in
the tensor-row exclusion of Aschbacher–Smith 3.2.9(4), printed pp.582–583.
The actual FSU application is in Chapter3/Section02/LinearThreeFourGraphTensor.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup

namespace Matrix.PSL3.LinearThree.OuterExtensions
/-- Diagram triviality is independent of an arbitrary PSL₃(4) quotient marking. -/
theorem diagramTrivial_of_equiv_four
    {F K : Type*} [Field F] [Finite F] [Field K] [Finite K]
    (hF : Nat.card F = 4) (hK : Nat.card K = 4)
    (e : PSL(3,F) ≃* PSL(3,K)) (a : MulAut PSL(3,F))
    (h : MulAut.congr e a ∈ diagramTrivial K) : a ∈ diagramTrivial F := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  let s : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF,hK])
  let j := Atlas.fieldEquivPSL 3 s
  let d : MulAut PSL(3,K) := j.symm.trans e
  have he : MulAut.congr e a = d * MulAut.congr j a * d⁻¹ := by
    ext x
    simp [d]
  rw [← diagramAction_ker K (n := 2) (by decide) hK] at h
  change diagramAction K (n := 2) (by decide) hK (MulAut.congr e a) = 1 at h
  rw [he,map_mul,map_mul,map_inv] at h
  have hj : diagramAction K (n := 2) (by decide) hK (MulAut.congr j a) = 1 := by
    have hh := congrArg (fun x : Equiv.Perm Bool =>
      (diagramAction K (n := 2) (by decide) hK d)⁻¹ * x *
        (diagramAction K (n := 2) (by decide) hK d)) h
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using hh
  rw [FieldTransport.diagramAction_congr (by decide) hF hK s a] at hj
  rw [← diagramAction_ker F (n := 2) (by decide) hF]
  exact hj
end Matrix.PSL3.LinearThree.OuterExtensions
