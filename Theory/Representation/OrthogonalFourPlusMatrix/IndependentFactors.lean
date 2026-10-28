module
public import Theory.Representation.OrthogonalFourPlusMatrix.NaturalTensor
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# Independent inner involutions in a binary determinant module

An additive involution commuting with one SL₂ factor is the action of an
involution from the opposite factor. Two nontrivial such operators on the
separate factors have common fixed space of dimension at most the field
degree n, so their binary fixed codimension is at least 3n.

The calculation uses the natural SL₂ commutant and conjugacy of involutions;
it works over every finite binary field. The large-actor estimate in
`LargeActorsGeneral` applies it to the two actual component kernels.
Source: Aschbacher--Smith H.1.1(2), 9.2.1, printed pp.378,730,
refs/quasithin.pdf.
-/

public noncomputable section
open Matrix Module Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace ClassicalOrthogonal.FourPlusMatrix.GeneralActors
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
@[expose] def binaryAction : Representation (ZMod 2) (PairSL (F := F)) (Mat (F := F)) :=
  restrictScalars (k := ZMod 2) representation
omit [Finite F] [CharP F 2] in
private theorem binaryAction_apply (g : PairSL (F := F)) (v : Mat (F := F)) :
    binaryAction g v = matrixAction g v := rfl
private def linearAction (g : PairSL (F := F)) : Mat (F := F) ≃ₗ[ZMod 2] Mat (F := F) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (binaryAction.asGroupHom g)
omit [CharP F 2] in
private theorem binary_finrank : finrank (ZMod 2) (Mat (F := F)) = 4 * finrank (ZMod 2) F := by
  rw [←Module.finrank_mul_finrank (ZMod 2) F]
  have hd : finrank F (Mat (F := F)) = 4 := by
    rw [Module.finrank_matrix]; norm_num
  rw [hd,Nat.mul_comm]
private def columnInsert (j : Fin 2) (v : Fin 2 → F) : Mat (F := F) :=
  fun i k => if k = j then v i else 0

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private lemma columnInsert_left (A : Mat (F := F)) (j : Fin 2) (v : Fin 2 → F) :
    A * columnInsert j v = columnInsert j (A.mulVec v) := by
  funext i k
  fin_cases k <;> fin_cases j <;>
    simp [columnInsert, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem left_centralizer (f : (Mat (F := F)) →+ (Mat (F := F)))
    (hleft : ∀ (A : SpecialLinearGroup (Fin 2) F) (M : (Mat (F := F))),
      f (A.val * M) = A.val * f M) :
    ∃ C : (Mat (F := F)), ∀ M, f M = M * C := by
  have hblock (j k : Fin 2) : ∃ c : F, ∀ v : Fin 2 → F,
      (fun i => f (columnInsert k v) i j) = c • v := by
    let b : (Fin 2 → F) →+ (Fin 2 → F) :=
      { toFun := fun v i => f (columnInsert k v) i j
        map_zero' := by
          have he : columnInsert k (0 : Fin 2 → F) = 0 := by funext i l; simp [columnInsert]
          change (fun i => f (columnInsert k 0) i j) = 0
          rw [he, f.map_zero]
          rfl
        map_add' := by
          intro v w
          have he : columnInsert k (v + w) = columnInsert k v + columnInsert k w := by
            funext i l
            by_cases h : l = k <;> simp [columnInsert, h]
          change (fun i => f (columnInsert k (v + w)) i j) = _
          rw [he, f.map_add]
          rfl }
    apply Representation.SL2NaturalOffenders.centralizer_scalar b
    intro A v
    change (fun i => f (columnInsert k (A.val.mulVec v)) i j) = _
    rw [← columnInsert_left, hleft]
    rfl
  choose c hc using hblock
  have hformula (M : Mat (F := F)) (i j : Fin 2) :
      f M i j = c j 0 * M i 0 + c j 1 * M i 1 := by
    have he : M = columnInsert 0 (fun i => M i 0) + columnInsert 1 (fun i => M i 1) := by
      funext i j
      fin_cases j <;> simp [columnInsert]
    have h0 := congrFun (hc j 0 (fun i => M i 0)) i
    have h1 := congrFun (hc j 1 (fun i => M i 1)) i
    conv_lhs => rw [he, map_add]
    exact congrArg₂ (· + ·) h0 h1
  let C : Mat (F := F) := fun i j => c j i
  have hformula' (M : Mat (F := F)) : f M = M * C := by
    funext i j
    rw [hformula]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp only [C]
    ring
  exact ⟨C,hformula'⟩

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem sl_one : (1 : SpecialLinearGroup (Fin 2) F).val = 1 := rfl

omit [Finite F] in
theorem left_centralizing_involution (t : (Mat (F := F)) ≃ₗ[ZMod 2] (Mat (F := F)))
    (ht : ∀ M, t (t M) = M)
    (hc : ∀ (a : SpecialLinearGroup (Fin 2) F) M,
      t (binaryAction (a,1) M) = binaryAction (a,1) (t M)) :
    ∃ b : SpecialLinearGroup (Fin 2) F, ∀ M, t M = binaryAction (1,b) M := by
  obtain ⟨C,hC⟩ := left_centralizer (show (Mat (F := F)) →+ (Mat (F := F)) from
    { toFun := t, map_zero' := t.map_zero, map_add' := t.map_add }) (by
    intro a M
    have hh := hc a M
    change t (a.val * M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val) =
      a.val * t M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val at hh
    simpa [sl_one] using hh)
  change ∀ M, t M = M*C at hC
  have hC2 : C*C=1 := by simpa only [hC, one_mul] using ht 1
  have hd : C.det = 1 := by
    have hh := congrArg Matrix.det hC2
    rw [Matrix.det_mul, Matrix.det_one] at hh
    exact CharTwo.sq_injective (by simpa only [pow_two,one_mul] using hh)
  let b : SpecialLinearGroup (Fin 2) F := ⟨C,hd⟩
  have hb : b⁻¹=b := inv_eq_of_mul_eq_one_left (Subtype.ext hC2)
  refine ⟨b,fun M => ?_⟩
  change t M = (1 : SpecialLinearGroup (Fin 2) F).val * M * b⁻¹.val
  rw [hb,sl_one,one_mul]
  exact hC M

omit [Finite F] in
theorem right_centralizing_involution (t : (Mat (F := F)) ≃ₗ[ZMod 2] (Mat (F := F)))
    (ht : ∀ M, t (t M) = M)
    (hc : ∀ (a : SpecialLinearGroup (Fin 2) F) M,
      t (binaryAction (1,a) M) = binaryAction (1,a) (t M)) :
    ∃ b : SpecialLinearGroup (Fin 2) F, ∀ M, t M = binaryAction (b,1) M := by
  let τ := (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) F F).restrictScalars (ZMod 2)
  let s := τ.trans (t.trans τ)
  have hs : ∀ M, s (s M) = M := by
    intro M
    change (t ((t M.transpose).transpose.transpose)).transpose=M
    rw [Matrix.transpose_transpose,ht,Matrix.transpose_transpose]
  have hsc : ∀ (a : SpecialLinearGroup (Fin 2) F) M,
      s (binaryAction (a,1) M) = binaryAction (a,1) (s M) := by
    intro a M
    have hh := hc (a.transpose⁻¹) M.transpose
    change t ((1 : SpecialLinearGroup (Fin 2) F).val * M.transpose *
      (a.transpose⁻¹)⁻¹.val) = (1 : SpecialLinearGroup (Fin 2) F).val *
      t M.transpose * (a.transpose⁻¹)⁻¹.val at hh
    simp only [sl_one, one_mul, inv_inv,
      SpecialLinearGroup.coe_transpose] at hh
    change (t ((a.val*M*(1 : SpecialLinearGroup (Fin 2) F)⁻¹.val).transpose)).transpose =
      a.val*(t M.transpose).transpose*(1 : SpecialLinearGroup (Fin 2) F)⁻¹.val
    simpa only [inv_one,sl_one,mul_one,Matrix.transpose_mul,
      Matrix.transpose_transpose] using congrArg Matrix.transpose hh
  obtain ⟨b,hb⟩ := left_centralizing_involution s hs hsc
  refine ⟨b⁻¹.transpose,fun M => ?_⟩
  have hh := hb M.transpose
  change (t M).transpose = (1 : SpecialLinearGroup (Fin 2) F).val * M.transpose * b⁻¹.val at hh
  change t M = (b⁻¹.transpose).val * M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val
  simpa only [sl_one,one_mul,inv_one,mul_one,Matrix.transpose_mul,
    Matrix.transpose_transpose,SpecialLinearGroup.coe_transpose] using congrArg Matrix.transpose hh
omit [Finite F] [CharP F 2] in
private theorem coordinates_of_fixed (v : (Mat (F := F)))
    (hl : binaryAction (SpecialLinearGroup.transvection zero_ne_one (1 : F), 1) v = v)
    (hr : binaryAction (1, (SpecialLinearGroup.transvection zero_ne_one (1 : F))⁻¹) v = v) :
    v 0 0 = 0 ∧ v 1 0 = 0 ∧ v 1 1 = 0 := by
  change (SpecialLinearGroup.transvection zero_ne_one (1 : F)).val * v *
    (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val = v at hl
  simp only [inv_one] at hl
  change (SpecialLinearGroup.transvection zero_ne_one (1 : F)).val * v * (1 : (Mat (F := F))) = v at hl
  rw [mul_one] at hl
  have hrow (j : Fin 2) : v 1 j = 0 := by
    have h := congrArg (fun w : (Mat (F := F)) => w 0 j) hl
    simpa [SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hcol (i : Fin 2) : v i 0 = 0 := by
    change (1 : SL(2,F)).val * v * ((SpecialLinearGroup.transvection zero_ne_one (1 : F))⁻¹)⁻¹.val = v at hr
    have h := congrArg (fun w : (Mat (F := F)) => w i 1) hr
    simpa [binaryAction_apply, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  exact ⟨hcol 0, hrow 0, hrow 1⟩

omit [CharP F 2] in
theorem finrank_le_degree_of_fixed_transvections (W : Submodule (ZMod 2) (Mat (F := F)))
    (hl : ∀ v ∈ W, binaryAction (SpecialLinearGroup.transvection zero_ne_one (1 : F), 1) v = v)
    (hr : ∀ v ∈ W, binaryAction (1, (SpecialLinearGroup.transvection zero_ne_one (1 : F))⁻¹) v = v) :
    finrank (ZMod 2) W ≤ finrank (ZMod 2) F := by
  let f : W →ₗ[ZMod 2] F := {
    toFun v := v.val 0 1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro v w he
    obtain ⟨hv00, hv10, hv11⟩ := coordinates_of_fixed (F := F) v.val (hl v.val v.property) (hr v v.property)
    obtain ⟨hw00, hw10, hw11⟩ := coordinates_of_fixed (F := F) w.val (hl w.val w.property) (hr w w.property)
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact hv00.trans hw00.symm
    · exact he
    · exact hv10.trans hw10.symm
    · exact hv11.trans hw11.symm
  exact LinearMap.finrank_le_finrank_of_injective hf

private def root : SL(2,F) := SpecialLinearGroup.transvection zero_ne_one (1 : F)

omit [Finite F] [Algebra (ZMod 2) F] in
private lemma root_square : root (F := F) * root = 1 := by
  rw [root, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

omit [Finite F] [Algebra (ZMod 2) F] in
private lemma root_inv : (root (F := F))⁻¹ = root := inv_eq_of_mul_eq_one_left root_square

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private lemma root_ne_one : root (F := F) ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL(2,F) => g.val 0 1) h
  simp [root, SpecialLinearGroup.transvection_coe] at hh

omit [Algebra (ZMod 2) F] in
private lemma exists_conjugate_root (a : SL(2,F)) (ha : a * a = 1) (hne : a ≠ 1) :
    ∃ c : SL(2,F), c * root * c⁻¹ = a := by
  let e := Theory.PSL2.sl2QuotientEquiv F
  have hoa : orderOf a = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨by rw [pow_two, ha], hne⟩
  have hoq : orderOf (root (F := F)) = 2 := (orderOf_eq_prime_iff (p := 2)).mpr
    ⟨by rw [pow_two, root_square], root_ne_one⟩
  have hp := Theory.PSL2.involutions_isConj (e root) (e a)
    ((e.orderOf_eq root).trans hoq) ((e.orderOf_eq a).trans hoa)
  have hc : IsConj root a := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      using e.symm.toMonoidHom.map_isConj hp
  exact isConj_iff.mp hc

/-- Two nonidentity inner involutions on separate factors fix at most one coefficient-field dimension. -/
theorem common_inner_fixed_finrank_le_degree (a b : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (binaryAction (a, 1) - 1) ⊓
      LinearMap.ker (binaryAction (1, b) - 1)) ≤ finrank (ZMod 2) F := by
  obtain ⟨c, hc⟩ := exists_conjugate_root a ha ha1
  obtain ⟨d, hd⟩ := exists_conjugate_root b hb hb1
  let W := LinearMap.ker (binaryAction (a, 1) - 1) ⊓ LinearMap.ker (binaryAction (1, b) - 1)
  let W' := W.map (binaryAction (c⁻¹, d⁻¹))
  have hleft (v : (Mat (F := F))) : binaryAction (root, 1) (binaryAction (c⁻¹, d⁻¹) v) =
      binaryAction (c⁻¹, d⁻¹) (binaryAction (a, 1) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    apply congrArg (fun g : (PairSL (F := F)) => binaryAction g v)
    apply Prod.ext
    · change root * c⁻¹ = c⁻¹ * a
      rw [← hc]
      group
    · exact one_mul d⁻¹ |>.trans (mul_one d⁻¹).symm
  have hright (v : (Mat (F := F))) : binaryAction (1, root) (binaryAction (c⁻¹, d⁻¹) v) =
      binaryAction (c⁻¹, d⁻¹) (binaryAction (1, b) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    apply congrArg (fun g : (PairSL (F := F)) => binaryAction g v)
    apply Prod.ext
    · exact one_mul c⁻¹ |>.trans (mul_one c⁻¹).symm
    · change root * d⁻¹ = d⁻¹ * b
      rw [← hd]
      group
  have hfixleft (v : (Mat (F := F))) (hv : v ∈ W') : binaryAction (root, 1) v = v := by
    obtain ⟨w, hw, rfl⟩ := hv
    rw [hleft, sub_eq_zero.mp hw.1, Module.End.one_apply]
  have hfixright (v : (Mat (F := F))) (hv : v ∈ W') : binaryAction (1, root⁻¹) v = v := by
    obtain ⟨w, hw, rfl⟩ := hv
    rw [root_inv, hright, sub_eq_zero.mp hw.2, Module.End.one_apply]
  have hbnd : finrank (ZMod 2) W' ≤ finrank (ZMod 2) F :=
    finrank_le_degree_of_fixed_transvections W' hfixleft hfixright
  have he : finrank (ZMod 2) W' = finrank (ZMod 2) W :=
    (linearAction (c⁻¹, d⁻¹)).finrank_map_eq W
  exact he.symm.le.trans hbnd

/-- The literal independent inner operators force binary displacement at least three field degrees. -/
theorem fixedCodim_ge_three_degree_of_independent_inner
    (A : Subgroup (Module.End (ZMod 2) (Mat (F := F)))ˣ)
    (a b : Matrix.SpecialLinearGroup (Fin 2) F) (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (haA : binaryAction.asGroupHom (a, 1) ∈ A) (hbA : binaryAction.asGroupHom (1, b) ∈ A) :
    3 * finrank (ZMod 2) F ≤ fixedCodim (Units.coeHom _) A := by
  let W := LinearMap.ker (binaryAction (a, 1) - 1) ⊓ LinearMap.ker (binaryAction (1, b) - 1)
  have hle : fixedSpace (Units.coeHom _) A ≤ W := by
    intro v hv
    exact ⟨sub_eq_zero.mpr (hv ⟨_, haA⟩), sub_eq_zero.mpr (hv ⟨_, hbA⟩)⟩
  have hh := (Submodule.finrank_mono hle).trans (common_inner_fixed_finrank_le_degree a b ha hb ha1 hb1)
  have he := fixedCodim_add_finrank (Units.coeHom (Module.End (ZMod 2) (Mat (F := F)))) A
  change finrank (ZMod 2) (fixedSpace (Units.coeHom (Module.End (ZMod 2) (Mat (F := F)))) A) ≤ finrank (ZMod 2) F at hh
  rw [binary_finrank] at he
  change 3 * finrank (ZMod 2) F ≤ fixedCodim (Units.coeHom (Module.End (ZMod 2) (Mat (F := F)))) A
  omega



end ClassicalOrthogonal.FourPlusMatrix.GeneralActors
