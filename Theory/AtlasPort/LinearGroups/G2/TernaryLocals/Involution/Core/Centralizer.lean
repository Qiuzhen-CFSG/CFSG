module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Core.Action

/-!
# Centralizer of the concrete quaternion generators

An actual involution-centralizing automorphism is reconstructed linearly from
its frame, using the octonion products in `columns`. Among all admissible
frames, the four quaternion commutation equations evaluated at the odd vector
`w` leave precisely the frames of the identity and the marked involution.
The finite calculation uses the compact, proved action formulas from Action
and is checked by the Lean kernel. Frame injectivity gives the group equality.

Source application: Aschbacher–Smith, I.4(G1), printed p.417, and Main Theorem
0.1.2(4), pp.3–4 (also pp.481–482). See Core.Action for coordinate attribution.
-/

public section

namespace Atlas.G2.TernaryLocals.Involution.CoreCalculation
open Atlas.SplitOctonion
set_option maxRecDepth 100000
private def frameMark (f : Frame) : Fin 3 → Carrier K :=
  ![fixedEmbed f.1.val.1, fixedEmbed f.1.val.2, oddEmbed f.2.val]

private def frameApply (f : Frame) (x : Carrier K) : Carrier K :=
  ∑ i : Fin 8, x i • columns (frameMark f 0) (frameMark f 1) (frameMark f 2) i

private theorem frameMark_encode (g : P) (k : Fin 3) :
    frameMark (encode g) k = g.val.val (marks k) := by
  fin_cases k
  · exact map_u g
  · exact map_v g
  · exact map_w g

private theorem frameApply_encode (g : P) (x : Carrier K) :
    frameApply (encode g) x = g.val.val x := by
  simp only [frameApply, frameMark_encode]
  change (∑ i : Fin 8, x i • columns (g.val.val u) (g.val.val v) (g.val.val w) i) = _
  simp_rw [← map_columns, columns_basis]
  calc
    _ = g.val.val (∑ i : Fin 8, x i • basisVector i) := by simp
    _ = g.val.val x := congrArg g.val.val (pi_eq_sum_univ' x).symm

set_option synthInstance.maxSize 512 in
/-- The commutation equations on admissible frames have only the two scalar solutions. -/
private theorem frame_centralizer_check (f : Frame)
    (hi : ∀ s j, frameApply f (qiApply s w) j = qiApply s (frameMark f 2) j)
    (hj : ∀ s j, frameApply f (qjApply s w) j = qjApply s (frameMark f 2) j) :
    f = encode 1 ∨ f = encode centralSign := by
  exact (by decide +kernel : ∀ f : Frame,
    (∀ s j, frameApply f (qiApply s w) j = qiApply s (frameMark f 2) j) →
    (∀ s j, frameApply f (qjApply s w) j = qjApply s (frameMark f 2) j) →
    f = encode 1 ∨ f = encode centralSign) f hi hj

theorem centralizer_quaternion_generators (g : P)
    (hi : ∀ s, quaternionI s * g = g * quaternionI s)
    (hj : ∀ s, quaternionJ s * g = g * quaternionJ s) :
    g = 1 ∨ g = centralSign := by
  have ei (s : Bool) (k : Fin 3) (j : Fin 8) :=
    congrArg (fun a : P => a.val.val (marks k) j) (hi s).symm
  have ej (s : Bool) (k : Fin 3) (j : Fin 8) :=
    congrArg (fun a : P => a.val.val (marks k) j) (hj s).symm
  have h := frame_centralizer_check (encode g) ?_ ?_
  · exact h.imp (fun h => encode_injective h) (fun h => encode_injective h)
  · intro s j
    rw [frameApply_encode, frameMark_encode]
    have e := ei s 2 j
    change g.val.val ((quaternionI s).val.val w) j =
      (quaternionI s).val.val (g.val.val w) j at e
    simpa [marks, qi_apply] using e
  · intro s j
    rw [frameApply_encode, frameMark_encode]
    have e := ej s 2 j
    change g.val.val ((quaternionJ s).val.val w) j =
      (quaternionJ s).val.val (g.val.val w) j at e
    simpa [marks, qj_apply] using e

end Atlas.G2.TernaryLocals.Involution.CoreCalculation
