module
public import Theory.Representation.BinaryAlternatingSixModels.TensorIrreducibility.Coordinates
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
# Cubic movement on the binary sixteen-dimensional tensor

Both conjugacy classes of elements of order three in S₆ have a
four-dimensional fixed space on the literal tensor of the two natural
four-spaces. We use the existing polar tensor coordinates and generator
matrices. Small binary matrix identities identify each fixed space with
F₂⁴; conjugacy handles every cubic element. The fixed index is 4096,
hence the cubic length is six.

The double-cycle matrix is computed through two separately checked
squares. The kernel-coordinate comparison is proved generically before
applying it to the concrete tensor, avoiding expansion of its action.
No enumeration of the 65536 tensor vectors is used.

Source: Aschbacher--Smith G.5.1--2 and 13.8.33, printed pp.342--343,967.
The source consumer is the Steinberg filtration comparison in Chapter13.
-/

public section
open Representation
open Theory.SpecificGroups.SymmetricSix
namespace BinaryAlternatingSix.CubicMovement
open TensorIrreducibility.Native
open TensorIrreducibility.Certificate (G H cols)
private def cubic (i : Fin 2) : S6 := ![gPerm,gPerm*gPerm*hPerm*hPerm] i
private def gSquared : Mat := cols #[9, 6, 2, 1, 37008, 24672, 8224, 4112, 2304, 1536, 512, 256, 144, 96, 32, 16]
private def hSquared : Mat := cols #[65295, 21765, 30471, 39177, 61695, 20565, 28791, 37017, 61680, 20560, 28784, 37008, 65520, 21840, 30576, 39312]
private def doubleMatrix : Mat := cols #[3276, 3003, 3549, 2184, 49164, 45067, 53261, 32776, 49152, 45056, 53248, 32768, 52224, 47872, 56576, 34816]
private theorem squares_checked : gSquared = G*G ∧ hSquared = H*H := by decide +kernel
private theorem double_checked : doubleMatrix = gSquared*hSquared := by decide +kernel
private theorem doubleMatrix_eq : doubleMatrix = G*G*H*H := by
  rw [double_checked,squares_checked.1,squares_checked.2]
  simp only [Matrix.mul_assoc]
private def cubicMatrix (i : Fin 2) : Mat := ![G,doubleMatrix] i
private def basisData : Fin 2 → Fin 4 → ℕ := ![![4224, 8256, 16480, 32912],![2461, 1097, 36937, 16596]]
private def readData : Fin 2 → Fin 16 → ℕ := ![![0, 0, 0, 0, 1, 2, 4, 8, 0, 0, 0, 0, 9, 6, 2, 1],![1, 2, 2, 0, 4, 8, 8, 0, 6, 11, 11, 0, 13, 6, 6, 0]]
private def basisMatrix (i : Fin 2) : Matrix (Fin 16) (Fin 4) (ZMod 2) :=
  fun r c => if (basisData i c).testBit r.val then 1 else 0
private def readMatrix (i : Fin 2) : Matrix (Fin 4) (Fin 16) (ZMod 2) :=
  fun r c => if (readData i c).testBit r.val then 1 else 0
private theorem cubic_certificate (i : Fin 2) :
    readMatrix i * basisMatrix i = 1 ∧
    cubicMatrix i * basisMatrix i = basisMatrix i ∧
    basisMatrix i * readMatrix i + cubicMatrix i * cubicMatrix i + cubicMatrix i = 1 := by
  fin_cases i <;> decide +kernel

private noncomputable def matrixFixedEquiv (i : Fin 2) :
    {v : Vec // (cubicMatrix i).mulVec v = v} ≃ (Fin 4 → ZMod 2) where
  toFun v := (readMatrix i).mulVec v.val
  invFun v := ⟨(basisMatrix i).mulVec v, by
    rw [Matrix.mulVec_mulVec,(cubic_certificate i).2.1]⟩
  left_inv v := by
    apply Subtype.ext
    have he := congrArg (fun M : Mat => M.mulVec v.val) (cubic_certificate i).2.2
    simp only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,Matrix.one_mulVec,v.property] at he
    have hz : v.val + v.val = 0 := by ext j; exact CharTwo.add_self_eq_zero (v.val j)
    simpa only [add_assoc,hz,add_zero] using he
  right_inv v := by
    change (readMatrix i).mulVec ((basisMatrix i).mulVec v) = v
    rw [Matrix.mulVec_mulVec,(cubic_certificate i).1,Matrix.one_mulVec]

private theorem coordinates_g (v : TensorModule) :
    coords (tensorAction gPerm v) = G.mulVec (coords v) := by
  have hm := matrix_action 2 v
  simpa only [actor,matrix,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,alternatingTensor,MonoidHom.comp_apply,g,h,Subgroup.subtype_apply] using hm

private theorem coordinates_h (v : TensorModule) :
    coords (tensorAction hPerm v) = H.mulVec (coords v) := by
  have hm := matrix_action 3 v
  simpa only [actor,matrix,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,alternatingTensor,MonoidHom.comp_apply,g,h,Subgroup.subtype_apply] using hm

private theorem cubic_coordinates (i : Fin 2) (v : TensorModule) :
    coords (tensorAction (cubic i) v) = (cubicMatrix i).mulVec (coords v) := by
  fin_cases i
  · exact coordinates_g v
  · change coords (tensorAction (gPerm*gPerm*hPerm*hPerm) v) = doubleMatrix.mulVec (coords v)
    rw [map_mul,map_mul,map_mul]
    simp only [Module.End.mul_apply]
    rw [coordinates_g,coordinates_g,coordinates_h,coordinates_h]
    change G.mulVec (G.mulVec (H.mulVec (H.mulVec (coords v)))) = _
    rw [doubleMatrix_eq]
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

private noncomputable def kernelCoordinates
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (T : Module.End (ZMod 2) W) (e : W ≃ₗ[ZMod 2] Vec) (M : Mat)
    (he : ∀ v, e (T v) = M.mulVec (e v)) :
    LinearMap.ker (T - 1) ≃ {v : Vec // M.mulVec v = v} where
  toFun v := ⟨e v.val, by
    rw [←he]
    have hv : T v.val = v.val := by
      simpa only [LinearMap.mem_ker,LinearMap.sub_apply,Module.End.one_apply,sub_eq_zero] using v.property
    exact congrArg e hv⟩
  invFun v := ⟨e.symm v.val, by
    rw [LinearMap.mem_ker,LinearMap.sub_apply,Module.End.one_apply,sub_eq_zero]
    apply e.injective
    rw [he,e.apply_symm_apply,v.property]⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

private noncomputable def tensorFixedEquiv (i : Fin 2) :
    LinearMap.ker (tensorAction (cubic i) - 1) ≃ (Fin 4 → ZMod 2) :=
  (kernelCoordinates (tensorAction (cubic i)) coords (cubicMatrix i)
    (cubic_coordinates i)).trans (matrixFixedEquiv i)

private theorem cubic_rank (i : Fin 2) :
    BinaryOffender.NaturalTensor.operatorFixedCodim (tensorAction (cubic i)) = 12 := by
  have hc : Nat.card (LinearMap.ker (tensorAction (cubic i) - 1)) = 16 := by
    rw [Nat.card_congr (tensorFixedEquiv i)]
    simp [Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hd : Module.finrank (ZMod 2) (LinearMap.ker (tensorAction (cubic i) - 1)) = 4 :=
    Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc
  have ht := BinaryOffender.NaturalTensor.operatorFixedCodim_add_finrank (tensorAction (cubic i))
  rw [hd,tensor_finrank] at ht
  omega

/-- Every element of order three moves twelve dimensions of the literal
sixteen-dimensional tensor module, for either six-letter cycle type. -/
theorem tensor_cubic_rank (a : S6) (ha : orderOf a = 3) :
    BinaryOffender.NaturalTensor.operatorFixedCodim (tensorAction a) = 12 := by
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order (ha ▸ Nat.prime_three)
  have hb := Equiv.Perm.sum_cycleType_le a
  rw [hn,ha,Multiset.sum_replicate] at hb
  norm_num [nsmul_eq_mul] at hb
  have hc : ∃ i : Fin 2, IsConj a (cubic i) := by
    have hle : n ≤ 1 := by omega
    interval_cases n
    · refine ⟨0,Equiv.Perm.isConj_iff_cycleType_eq.mpr ?_⟩
      rw [hn,ha]
      decide +kernel
    · refine ⟨1,Equiv.Perm.isConj_iff_cycleType_eq.mpr ?_⟩
      rw [hn,ha]
      decide +kernel
  obtain ⟨i,hi⟩ := hc
  have he : BinaryOffender.NaturalTensor.operatorFixedCodim (tensorAction a) =
      BinaryOffender.NaturalTensor.operatorFixedCodim (tensorAction (cubic i)) := by
    obtain ⟨b,hb⟩ := isConj_iff.mp hi
    let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) TensorModule
      (tensorAction.asGroupHom b)
    apply BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv _ _ e
    intro v
    have hh : b*a=cubic i*b := mul_inv_eq_iff_eq_mul.mp hb
    have he := LinearMap.congr_fun (congrArg tensorAction hh) v
    simp only [map_mul,Module.End.mul_apply] at he
    exact he
  exact he.trans (cubic_rank i)

/-- The genuine tensor action has cubic length six on every subgroup of
order three. The action and subgroup embedding are retained. -/
theorem tensor_cubic_length (A : Subgroup S6) (hA : Nat.card A = 3) :
    letI := Representation.BinaryFixedPoints.action (tensorAction.comp A.subtype)
    FixedPoints.cubicLength A (Multiplicative TensorModule) = 6 := by
  let ρ : Representation (ZMod 2) A TensorModule := tensorAction.comp A.subtype
  let : Finite TensorModule := Finite.of_equiv Vec coords.toEquiv.symm
  let := Representation.BinaryFixedPoints.action ρ
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := A)
  have hao : orderOf a = 3 := by
    have ht : Subgroup.zpowers a = ⊤ := by
      apply top_unique
      exact fun x _ => ha x
    rw [← Nat.card_zpowers,ht,Subgroup.card_top,hA]
  have hv : orderOf (a : S6) = 3 := (orderOf_injective A.subtype A.subtype_injective a).trans hao
  have hk : ρ.invariants = LinearMap.ker (tensorAction (a : S6) - 1) := by
    ext v
    rw [ρ.mem_invariants_iff_of_forall_mem_zpowers a ha]
    simp only [LinearMap.mem_ker,LinearMap.sub_apply,Module.End.one_apply,sub_eq_zero]
    rfl
  have hd := BinaryOffender.NaturalTensor.operatorFixedCodim_add_finrank (tensorAction (a : S6))
  rw [tensor_cubic_rank (a : S6) hv,tensor_finrank] at hd
  have hdim : Module.finrank (ZMod 2) ρ.invariants = 4 := by rw [hk]; omega
  have hc : Nat.card ρ.invariants = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim,Nat.card_zmod]
    norm_num
  have hm := Representation.BinaryFixedPoints.fixedIndex_mul_card ρ
  have ht : Nat.card TensorModule = 65536 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),tensor_finrank,Nat.card_zmod]
    norm_num
  rw [hc,ht] at hm
  have hidx : Representation.BinaryFixedPoints.fixedIndex ρ = 4096 := by omega
  change Nat.log 4 (Representation.BinaryFixedPoints.fixedIndex ρ) = 6
  rw [hidx]
  decide

end BinaryAlternatingSix.CubicMovement
