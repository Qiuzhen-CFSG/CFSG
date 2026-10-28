module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CoreCertificateMasks

/-!
# Every core-by-natural extension is a coboundary

The finite mask identities give explicit linear formulas for the correcting
rectangular matrix. Evaluating them on arbitrary blocks satisfying
the actual square, commute, and braid relations proves the normal form.
No finite enumeration of cochains or trusted computation is used.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
open MaskMatrices CoreCertificateMasks CoreCertificateData

private def flatten (B : Fin 7 → CoreRect) (k : Fin 294) : ZMod 2 :=
  B ⟨k.val/42,by omega⟩ ⟨k.val%42/6,by omega⟩ ⟨k.val%6,by omega⟩

private theorem input_evaluate (B : Fin 7 → CoreRect) (i : Fin 7) :
    evaluate (flatten B) (input i) = B i := by
  funext r c
  change Mask.evalRow (flatten B) (Mask.unit (index i r c)) = B i r c
  rw [Mask.evalRow_unit]
  unfold flatten index
  congr 3 <;> dsimp only <;> omega

private theorem decode_rows (i : Fin 7) : decode (rows i) = A i := rfl
private theorem decode_coreRows (i : Fin 7) : decode (coreRows i) = CoreA i := rfl

private theorem relation_evaluate_zero (B : Fin 7 → CoreRect) (h : CoreRelations B)
    (typ : Fin 3) (i j : Fin 7)
    (hc : typ = 1 → i.val + 1 < j.val)
    (hb : typ = 2 → j.val = i.val + 1) :
    evaluate (flatten B) (relation typ i j) = 0 := by
  have ht : typ = 0 ∨ typ = 1 ∨ typ = 2 := by omega
  rcases ht with rfl | rfl | rfl
  · simpa only [relation,↓reduceIte,evaluate_add,evaluate_left,evaluate_right,
      input_evaluate,decode_rows,decode_coreRows] using h.square i
  · simp only [relation,show (1 : Fin 3) ≠ 0 from by decide,↓reduceIte,
      evaluate_add,evaluate_left,evaluate_right,input_evaluate,decode_rows,decode_coreRows]
    rw [h.commute i j (hc rfl)]
    ext r c
    simp only [Matrix.add_apply,Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · simp only [relation,show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide,↓reduceIte,
      evaluate_add,evaluate_left,evaluate_right,input_evaluate,decode_rows,decode_coreRows,←Matrix.mul_assoc]
    rw [h.braid i j (hb rfl)]
    ext r c
    simp only [Matrix.add_apply,Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _

private theorem constraints_zero (B : Fin 7 → CoreRect) (h : CoreRelations B) :
    ∀ k : Fin 252, Mask.evalRow (flatten B) (constraintMasks k) = 0 := by
  intro k
  rw [←constraintMasks_spec k]
  have hp := constraintPlaces_valid k
  exact congrFun (congrFun (relation_evaluate_zero B h
    (constraintPlaces k).1 (constraintPlaces k).2.1 (constraintPlaces k).2.2.1 hp.1 hp.2)
      (constraintPlaces k).2.2.2.1) (constraintPlaces k).2.2.2.2

/-- Every rectangular off-diagonal solution is a coboundary. Thus the
natural six-space has no nonsplit extension by the augmentation core. -/
theorem core_relations_coboundary (B : Fin 7 → CoreRect) (h : CoreRelations B) :
    ∃ D : CoreRect, ∀ i : Fin 7, B i = CoreA i * D + D * A i := by
  let d := flatten B
  let D := evaluate d correction
  refine ⟨D,?_⟩
  have hz (v : BitVec 252) : Mask.evalRow d (Mask.substitute constraintMasks v) = 0 := by
    rw [Mask.evalRow_substitute]
    have hzero : ∀ k, Mask.evalRow d (constraintMasks k) = 0 := constraints_zero B h
    simp_rw [hzero]
    simp only [Mask.evalRow,ite_self,Finset.sum_const_zero]
  intro i
  have hout : evaluate d (correctionOutput i) = CoreA i * D + D * A i := by
    simp only [correctionOutput,evaluate_add,evaluate_left,evaluate_right,
      decode_rows,decode_coreRows]
    rfl
  rw [←hout,←input_evaluate B i]
  funext r k
  change Mask.evalRow d (input i r k) = Mask.evalRow d (correctionOutput i r k)
  rw [correction_certificate,Mask.evalRow_xor,hz,add_zero]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
