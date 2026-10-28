module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CertificateMasks

/-!
# Every natural-six self-extension is a coboundary plus parity

The finite mask identities give explicit linear formulas for the correcting
matrix and parity parameter. Evaluating them on arbitrary blocks satisfying
the actual square, commute, and braid relations proves the normal form.
No finite enumeration of cochains or trusted computation is used.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
open MaskMatrices CertificateMasks CertificateData

private def flatten (B : Fin 7 → Mat) (k : Fin 252) : ZMod 2 :=
  B ⟨k.val/36,by omega⟩ ⟨k.val%36/6,by omega⟩ ⟨k.val%6,by omega⟩

private theorem input_evaluate (B : Fin 7 → Mat) (i : Fin 7) :
    evaluate (flatten B) (input i) = B i := by
  funext r c
  change Mask.evalRow (flatten B) (Mask.unit (index i r c)) = B i r c
  rw [Mask.evalRow_unit]
  unfold flatten index
  congr 3 <;> dsimp only <;> omega

private theorem decode_rows (i : Fin 7) : decode (rows i) = A i := rfl

private theorem relation_evaluate_zero (B : Fin 7 → Mat) (h : Relations B)
    (typ : Fin 3) (i j : Fin 7)
    (hc : typ = 1 → i.val + 1 < j.val)
    (hb : typ = 2 → j.val = i.val + 1) :
    evaluate (flatten B) (relation typ i j) = 0 := by
  have ht : typ = 0 ∨ typ = 1 ∨ typ = 2 := by omega
  rcases ht with rfl | rfl | rfl
  · simpa only [relation,↓reduceIte,evaluate_add,evaluate_left,evaluate_right,
      input_evaluate,decode_rows] using h.square i
  · simp only [relation,show (1 : Fin 3) ≠ 0 from by decide,↓reduceIte,
      evaluate_add,evaluate_left,evaluate_right,input_evaluate,decode_rows]
    rw [h.commute i j (hc rfl)]
    funext r c
    simp only [Matrix.add_apply,Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · simp only [relation,show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide,↓reduceIte,
      evaluate_add,evaluate_left,evaluate_right,input_evaluate,decode_rows,←Matrix.mul_assoc]
    rw [h.braid i j (hb rfl)]
    funext r c
    simp only [Matrix.add_apply,Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _

private theorem constraints_zero (B : Fin 7 → Mat) (h : Relations B) :
    ∀ k : Fin 216, Mask.evalRow (flatten B) (constraintMasks k) = 0 := by
  intro k
  rw [←constraintMasks_spec k]
  have hp := constraintPlaces_valid k
  exact congrFun (congrFun (relation_evaluate_zero B h
    (constraintPlaces k).1 (constraintPlaces k).2.1 (constraintPlaces k).2.2.1 hp.1 hp.2)
      (constraintPlaces k).2.2.2.1) (constraintPlaces k).2.2.2.2

set_option maxRecDepth 10000 in
/-- Every off-diagonal solution of the actual adjacent-transposition relations
is a coboundary plus a scalar multiple of the parity self-extension. -/
theorem normal_form (B : Fin 7 → Mat) (h : Relations B) :
    ∃ D : Mat, ∃ c : ZMod 2, ∀ i : Fin 7,
      B i = A i * D + D * A i + c • A i := by
  let d := flatten B
  let D := evaluate d correction
  let c := Mask.evalRow d parity
  refine ⟨D,c,?_⟩
  have hz (v : BitVec 216) : Mask.evalRow d (Mask.substitute constraintMasks v) = 0 := by
    have he : (fun k => Mask.evalRow d (constraintMasks k)) = fun _ => 0 :=
      funext (constraints_zero B h)
    rw [Mask.evalRow_substitute,he]
    simp only [Mask.evalRow,ite_self,Finset.sum_const_zero]
  intro i
  have hout : evaluate d (correctionOutput i) = A i * D + D * A i + c • A i := by
    simp only [correctionOutput,evaluate_add,evaluate_left,evaluate_right,decode_rows]
    change A i * D + D * A i + evaluate d
      (fun r k => if (rows i r).getLsbD k.val then parity else 0) = _
    apply congrArg (fun X : Mat => A i * D + D * A i + X)
    funext r k
    change Mask.evalRow d (if (rows i r).getLsbD k.val then parity else 0) =
      c * (if (rows i r).getLsbD k.val then 1 else 0)
    cases (rows i r).getLsbD k.val
    · change Mask.evalRow d (0 : BitVec 252) = c * 0
      rw [mul_zero]
      exact Mask.evalRow_zero d
    · change c = c * 1
      exact (mul_one c).symm
  rw [←hout,←input_evaluate B i]
  funext r k
  change Mask.evalRow d (input i r k) = Mask.evalRow d (correctionOutput i r k)
  rw [correction_certificate,Mask.evalRow_xor,hz,add_zero]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
