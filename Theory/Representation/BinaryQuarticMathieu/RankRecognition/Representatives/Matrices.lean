module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Slices
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Arithmetic
/-!
# The actual contraction matrices in packed coordinates

The representative slices are the quartic's certified values on standard basis
vectors. Linearity in the second argument and XOR decoding therefore produce
exactly the matrix whose row j and column i evaluate the contraction on e_i,e_j.
This is the semantic link used by every finite rank certificate.
-/

@[expose] public section
namespace BinaryQuarticMathieu.RankRecognition.Representatives

def contractionRows (c : Fin 3) (n : Word) : Rows :=
  fun j => rowProduct n.val (fun k => sliceRows c k j)

lemma second_expansion (Q : Form) (v w x y : U) :
    Q ![v,w,x,y] = ∑ k, w k * Q ![v,basisVector k,x,y] := by
  let L : U →ₗ[F] F :=
    { toFun := fun w => Q ![v,w,x,y]
      map_add' := fun a b => (Q.curryLeft v).map_vecCons_add ![x,y] a b
      map_smul' := fun r a => (Q.curryLeft v).map_vecCons_smul ![x,y] r a }
  have hw : ∑ k, w k • basisVector k = w := by
    simpa [Pi.basisFun_apply, basisVector] using (Pi.basisFun F (Fin 10)).sum_repr w
  change L w = _
  conv_lhs => rw [← hw]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem matrix_contractionRows (c : Fin 3) (n : Word) :
    matrix (contractionRows c n) = contractionMatrix quartic (decode (representative c.succ)) (decode n) := by
  ext j i
  rw [representative_coordinate]
  change bit (rowProduct n.val (fun k => sliceRows c k j)) i.val = _
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [contractionMatrix, second_expansion]
  apply Finset.sum_congr rfl
  intro k _
  rw [slice_value]
  change bit (if n.val.testBit k.val then sliceRows c k j else 0) i.val =
    bit n.val k.val * bit (sliceRows c k j) i.val
  cases h : n.val.testBit k.val <;> simp [bit, h]

end BinaryQuarticMathieu.RankRecognition.Representatives
