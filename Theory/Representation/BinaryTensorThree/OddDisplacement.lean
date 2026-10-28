module
public import Theory.Representation.BinaryTensorThree.Normalizer
public import Theory.Representation.TensorThreeFixedSpace
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Odd displacement and small fixed subspaces in the binary tensor

An odd-order element lies in the two-factor base. Two nonscalar factors
fix at most five dimensions by the spectral tensor bound. If one factor
is the identity, its three copies fix at most three dimensions: a binary
operator with displacement at most one has square one. Thus every
nonidentity odd-order tensor actor moves at least four dimensions.
Cauchy's theorem makes the pointwise action on a subspace of codimension
at most three a two-group.

The original minimal-module application is in QuietTensorSmallCentralizer,
with the full ambient action kernel retained. This supplies H.4.12(3)'s
local centralizer input to the strict-r argument of 8.3.11.
Source: Aschbacher--Smith H.4.12(3) and 8.3.11, printed pp.385,726.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation.BinaryOffender
open scoped TensorProduct
namespace BinaryTensorThree
open BinaryPermutation.FiveTensorSquare

private theorem natural_fixed_le_one (a : Factor) (ho : Odd (orderOf a)) (ha : a ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.ker (a.toLinearMap - LinearMap.id)) ≤ 1 := by
  by_contra hn
  have hd := (a.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  have hdim : Module.finrank (ZMod 2) Natural = 3 := by simp
  have hr : Module.finrank (ZMod 2) (a.toLinearMap - LinearMap.id).range ≤ 1 := by omega
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | h1
    · exact hz
    have hv : a v = 0 := by
      change a.toLinearMap v = 0
      rw [he, LinearMap.transvection.apply,h1,one_smul,ZModModule.add_self]
    have hz := a.map_eq_zero_iff.mp hv
    rw [hz,map_zero] at h1
    exact (zero_ne_one h1).elim
  have hsq : a^2 = 1 := by
    apply LinearEquiv.ext
    intro x
    change a (a x) = x
    have hx (x : Natural) : a x = x + f x • v :=
      congrArg (fun l : Natural →ₗ[ZMod 2] Natural => l x) he
    simp only [hx,map_add,map_smul,hfv,smul_zero,add_zero]
    simp [add_assoc,ZModModule.add_self]
  exact ha (orderOf_eq_one_iff.mp (ho.coprime_two_right.eq_one_of_dvd
    (orderOf_dvd_of_pow_eq_one hsq)))

private def factorMatrix (a : Factor) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  LinearMap.toMatrixAlgEquiv' a.toLinearMap

private theorem factorMatrix_pow (a : Factor) (n : ℕ) :
    factorMatrix (a^n) = factorMatrix a ^ n := by
  change LinearMap.toMatrixAlgEquiv' ((a^n).toLinearMap) = _
  have he : (a^n).toLinearMap = a.toLinearMap ^ n := by
    induction n with
    | zero => rfl
    | succ n hn => simp only [pow_succ]; change (a^n).toLinearMap * a.toLinearMap = _; rw [hn]
  rw [he,map_pow]; rfl

private theorem factorMatrix_one : factorMatrix (1 : Factor) = 1 := by
  change LinearMap.toMatrixAlgEquiv' (1 : Module.End (ZMod 2) Natural) = 1
  exact map_one _

private theorem factorMatrix_nonscalar (a : Factor) (ha : a ≠ 1) :
    ¬ ∃ c : ZMod 2, factorMatrix a = c • 1 := by
  rintro ⟨c,hc⟩
  have he : a.toLinearMap = c • (1 : Module.End (ZMod 2) Natural) := by
    apply LinearMap.toMatrixAlgEquiv'.injective
    simpa only [factorMatrix,map_smul,map_one] using hc
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl
  · have hz : a (Pi.single 0 1) = 0 := by rw [show a (Pi.single 0 1) = a.toLinearMap (Pi.single 0 1) from rfl,he]; simp
    have hh := congrFun (a.map_eq_zero_iff.mp hz) 0
    simp at hh
  · apply ha
    apply LinearEquiv.toLinearMap_injective
    exact he.trans (one_smul _ _)

private theorem baseAction_matrix (a b : Factor) (X : Space) :
    baseAction (a,b) X = factorMatrix a * X * (factorMatrix b).transpose := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [baseAction_tmul]
    change Matrix.vecMulVec (a x) (b y) = _
    change Matrix.vecMulVec (a.toLinearMap x) (b.toLinearMap y) = _
    rw [←LinearMap.toMatrix'_mulVec,←LinearMap.toMatrix'_mulVec]
    change Matrix.vecMulVec ((factorMatrix a).mulVec x) ((factorMatrix b).mulVec y) =
      factorMatrix a * Matrix.vecMulVec x y * (factorMatrix b).transpose
    rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_transpose]
  | add x y hx hy => simp [map_add,Matrix.mul_add,Matrix.add_mul,hx,hy]

private theorem left_fixed_le_three (a : Factor) (ho : Odd (orderOf a)) (ha : a ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace action (zpowers (baseEmbedding (a,1)))) ≤ 3 := by
  let F := LinearMap.ker (a.toLinearMap - LinearMap.id)
  let W := fixedSpace action (zpowers (baseEmbedding (a,1)))
  have hcolumn (X : W) (j : Fin 3) : (fun i => X.val i j) ∈ F := by
    have hx := (mem_fixedSpace_zpowers_iff action _ X.val).mp X.property
    change baseAction (a,1) X.val = X.val at hx
    rw [baseAction_matrix,factorMatrix_one,Matrix.transpose_one,mul_one] at hx
    apply sub_eq_zero.mpr
    ext i
    have hij := congrArg (fun Y : Space => Y i j) hx
    change a.toLinearMap (fun k => X.val k j) i = _
    rw [←LinearMap.toMatrix'_mulVec]
    exact hij
  let f : W →ₗ[ZMod 2] (Fin 3 → F) :=
    { toFun := fun X j => ⟨fun i => X.val i j,hcolumn X j⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro X Y h
    apply Subtype.ext
    ext i j
    exact congrArg (fun z : Fin 3 → F => (z j).val i) h
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  have hb := natural_fixed_le_one a ho ha
  have hdim : Module.finrank (ZMod 2) (Fin 3 → F) = 3 * Module.finrank (ZMod 2) F := by
    simp [Module.finrank_pi_fintype]
  rw [hdim] at hd
  change Module.finrank (ZMod 2) F ≤ 1 at hb
  change Module.finrank (ZMod 2) W ≤ 3
  omega

private theorem base_odd_fixed_le_five (a b : Factor)
    (ho : Odd (orderOf (a,b))) (hne : (a,b) ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace action (zpowers (baseEmbedding (a,b)))) ≤ 5 := by
  have hoa : Odd (orderOf a) := ho.of_dvd_nat orderOf_fst_dvd_orderOf
  have hob : Odd (orderOf b) := ho.of_dvd_nat orderOf_snd_dvd_orderOf
  by_cases hb : b = 1
  · subst b
    exact (left_fixed_le_three a hoa (fun h => hne (Prod.ext h rfl))).trans (by decide)
  by_cases ha : a = 1
  · subst a
    let f : fixedSpace action (zpowers (baseEmbedding (1,b))) →ₗ[ZMod 2]
        fixedSpace action (zpowers (baseEmbedding (b,1))) :=
      { toFun := fun X => ⟨flip X.val,by
          apply (mem_fixedSpace_zpowers_iff action _ _).mpr
          have hx := (mem_fixedSpace_zpowers_iff action _ X.val).mp X.property
          change baseAction (b,1) (flip X.val) = flip X.val
          exact (flip_baseAction (1,b) X.val).symm.trans (congrArg flip hx)⟩
        map_add' := by intros; apply Subtype.ext; exact map_add flip _ _
        map_smul' := by intros; apply Subtype.ext; exact map_smul flip _ _ }
    have hf : Function.Injective f := fun _ _ h => Subtype.ext
      (flip.injective (congrArg Subtype.val h))
    exact (LinearMap.finrank_le_finrank_of_injective hf).trans
      ((left_fixed_le_three b hob hb).trans (by decide))
  apply Representation.TensorThreeFixedSpace.matrix_fixed_finrank_le_five_of_odd
    (factorMatrix a) (factorMatrix b) (orderOf a) (orderOf b) hoa hob
    (by rw [←factorMatrix_pow,pow_orderOf_eq_one,factorMatrix_one])
    (by rw [←factorMatrix_pow,pow_orderOf_eq_one,factorMatrix_one])
    (factorMatrix_nonscalar a ha) (factorMatrix_nonscalar b hb)
    (fixedSpace action (zpowers (baseEmbedding (a,b)))).subtype Subtype.val_injective
  intro X
  rw [←baseAction_matrix]
  exact (mem_fixedSpace_zpowers_iff action _ X.val).mp X.property

/-- Every nonidentity odd-order tensor actor moves at least four dimensions. -/
theorem odd_fixedCodim_ge_four (g : Group) (ho : Odd (orderOf g)) (hne : g ≠ 1) :
    4 ≤ fixedCodim action (zpowers g) := by
  let eW := MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective⟩
  let w := eW.symm g
  have hw : wreathHom w = g := eW.apply_symm_apply g
  have hor : Odd (orderOf w.right) :=
    ((eW.symm.orderOf_eq g).symm ▸ ho).of_dvd_nat
      (orderOf_map_dvd RegularWreathProduct.rightHom w)
  have hr : w.right = 1 := by
    rcases index_cases w.right with hh | hh
    · exact hh
    · rw [hh] at hor
      have hs : orderOf swapIndex = 2 := orderOf_eq_prime (by decide +kernel) swapIndex_ne_one
      rw [hs] at hor
      exact False.elim ((by decide : ¬ Odd (2 : ℕ)) hor)
  have he : baseEmbedding (w.left 1,w.left swapIndex) = g := by
    change wreathMap w = g at hw
    simpa only [wreathMap,hr,ite_true] using hw
  have hi : Function.Injective baseEmbedding := fun _ _ h =>
    baseAction_injective (congrArg Subtype.val h)
  have hob : Odd (orderOf (w.left 1,w.left swapIndex)) := by
    rw [←orderOf_injective baseEmbedding hi,he]
    exact ho
  have hb := base_odd_fixed_le_five (w.left 1) (w.left swapIndex) hob
    (fun h => hne (he.symm.trans (by rw [h,map_one])))
  rw [he] at hb
  have hd := fixedCodim_add_finrank action (zpowers g)
  have hdim : Module.finrank (ZMod 2) Space = 9 := by rw [Module.finrank_matrix]; norm_num
  omega

/-- A tensor subgroup fixing a subspace of codimension at most three is a two-group. -/
theorem isTwoGroup_of_fixedCodim_le_three (A : Subgroup Group)
    (hc : fixedCodim action A ≤ 3) : IsPGroup 2 A := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p = 2 := by
    by_contra hp2
    let : Fact p.Prime := ⟨hpp⟩
    obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpd
    have ho : Odd (orderOf a.val) := by
      rw [Subgroup.orderOf_coe,ha]
      exact hpp.odd_of_ne_two hp2
    have hne : a.val ≠ 1 := by
      intro h
      have h1 : a = 1 := Subtype.ext h
      rw [h1,orderOf_one] at ha
      exact hpp.ne_one ha.symm
    have hb := odd_fixedCodim_ge_four a.val ho hne
    have hu := Submodule.finrank_mono (fixedSpace_antitone action (zpowers_le.mpr a.property))
    have hd1 := fixedCodim_add_finrank action A
    have hd2 := fixedCodim_add_finrank action (zpowers a.val)
    omega
  simpa only [hp2] using (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩ :
    2 ∈ Nat.primeFactors 2)

end BinaryTensorThree
