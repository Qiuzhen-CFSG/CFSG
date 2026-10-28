module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SL2.NormalMonolith
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Nontrivial prime-field SL₂ actions on elementary abelian planes

For p > 3, every nontrivial action of SL₂(p) on an elementary abelian plane
of odd characteristic is faithful and its central involution acts by inversion.
Perfectness forces determinant one. If the central involution were killed,
a square root of it would act as a scalar; its noncentral commutator with a
transvection would then be killed, contradicting quasisimplicity.

Source: Aschbacher--Smith, A.1.33(2), printed p.29. The basis transport follows
`Theory.SpecificGroups.SL2.DegreeTwoActions`.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup.PrimePlaneAction

variable {p : ℕ} [Fact p.Prime]

/-- SL₂ over a prime field with more than three elements is perfect. -/
public theorem perfect (hp : 3 < p) : Group.IsPerfect (SL(2, ZMod p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hsq : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by linear_combination h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  exact ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩

private def w : SL(2, ZMod p) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
private def u : SL(2, ZMod p) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem w_sq : (w : SL(2, ZMod p)) ^ 2 = -1 := by
  apply Subtype.ext
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem commutator_not_central : ⁅(w : SL(2, ZMod p)), (u : SL(2, ZMod p))⁆ ∉ center SL(2, ZMod p) := by
  intro h
  have hh := Subgroup.mem_center_iff.mp h u
  have hcomm : ⁅(w : SL(2, ZMod p)), (u : SL(2, ZMod p))⁆ =
      ⟨!![1, -1; -1, 2], by norm_num [Matrix.det_fin_two_of]⟩ := by
    apply Subtype.ext
    change (!![0, 1; -1, 0] * !![1, 1; 0, 1] *
      Matrix.adjugate !![0, 1; -1, 0] * Matrix.adjugate !![1, 1; 0, 1] :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, -1; -1, 2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hcomm] at hh
  have h00 := congrArg (fun a : SL(2, ZMod p) => a 0 0) hh
  change (!![1, 1; 0, 1] * !![1, -1; -1, 2] : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 =
    (!![1, -1; -1, 2] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 at h00
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem det_eq_one {F : Type*} [Field F] (hp : 3 < p)
    (f : SL(2, ZMod p) →* GeneralLinearGroup (Fin 2) F) (g : SL(2, ZMod p)) :
    (f g).det = 1 := by
  let := perfect hp
  let d := GeneralLinearGroup.det.comp f
  have h : d = 1 := by
    apply MonoidHom.ker_eq_top_iff.mp
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top (G := SL(2, ZMod p))]
    exact Abelianization.commutator_subset_ker d
  exact DFunLike.congr_fun h g

/-- A nontrivial representation of SL₂(p) of degree two detects `-1`. -/
public theorem map_neg_one_of_nontrivial {F : Type*} [Field F]
    (hp : 3 < p) (hF : (2 : F) ≠ 0)
    (f : SL(2, ZMod p) →* GeneralLinearGroup (Fin 2) F) (hf : f ≠ 1) : f (-1) = -1 := by
  let : IsQuasisimple (SL(2, ZMod p)) := {
    toIsPerfect := perfect hp
    simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod p) (by
      rw [Nat.card_zmod]; omega) }
  have hne : f (-1) ≠ 1 := by
    intro hz
    have hwsq : f w ^ 2 = 1 := by rw [← map_pow, w_sq (p := p), hz]
    have hw := GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      hF (f w) hwsq (det_eq_one hp f w)
    have hcomm : ⁅(w : SL(2, ZMod p)), (u : SL(2, ZMod p))⁆ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      rcases hw with hw | hw <;> rw [hw] <;> simp
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with h | h
    · exact commutator_not_central (h hcomm)
    · exact hf (MonoidHom.ker_eq_top_iff.mp h)
  have hsq : f (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  exact (GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
    hF (f (-1)) hsq (det_eq_one hp f (-1))).resolve_left hne

/-- A nontrivial SL₂(p) action on a prime elementary plane is faithful and
its central involution acts by inversion. -/
public theorem faithful_and_inverts {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian p V] (hp : 3 < p) (hc : Nat.card V = p ^ 2)
    (ρ : SL(2, ZMod p) →* MulAut V) (hρ : ρ ≠ 1) :
    Function.Injective ρ ∧ ∀ v, ρ (-1) v = v⁻¹ := by
  classical
  have hpow : p ^ Module.finrank (ZMod p) (Additive V) = p ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    change Nat.card V = _ at hsize
    simpa only [Nat.card_zmod, hc] using hsize.symm
  have hdim : Module.finrank (ZMod p) (Additive V) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt hpow
  let autLinear : MulAut V ≃* (Additive V ≃ₗ[ZMod p] Additive V) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive V) hdim
  let d : GeneralLinearGroup (Fin 2) (ZMod p) ≃* (Additive V ≃ₗ[ZMod p] Additive V) :=
    (GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V))
  let e : MulAut V ≃* GeneralLinearGroup (Fin 2) (ZMod p) := autLinear.trans d.symm
  have hf : e.toMonoidHom.comp ρ ≠ 1 := by
    intro h
    apply hρ
    ext g : 1
    apply e.injective
    simpa using DFunLike.congr_fun h g
  have hp2 : (2 : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have he := map_neg_one_of_nontrivial hp hp2 (e.toMonoidHom.comp ρ) hf
  have hne : ρ (-1) ≠ 1 := by
    intro h
    have hh : (-1 : GeneralLinearGroup (Fin 2) (ZMod p)) = 1 := by
      simpa [h] using he.symm
    have hz := congrArg (fun A : GeneralLinearGroup (Fin 2) (ZMod p) => A.val 0 0) hh
    change (-1 : ZMod p) = 1 at hz
    exact hp2 (by linear_combination -hz)
  constructor
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp (eq_bot_of_neg_one_not_mem hp2 ρ.ker hne)
  · have hlin : autLinear (ρ (-1)) =
        (GeneralLinearGroup.toLin' b (-1)).toLinearEquiv := by
      change autLinear (ρ (-1)) = d (-1)
      simpa [e] using congrArg d he
    intro v
    have hv := congrArg (fun a : Additive V ≃ₗ[ZMod p] Additive V => a (Additive.ofMul v)) hlin
    change Additive.ofMul (ρ (-1) v) = _ at hv
    rw [GeneralLinearGroup.toLin'_apply] at hv
    have hm : (↑(-1 : GeneralLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := rfl
    rw [hm, Matrix.neg_mulVec, Matrix.one_mulVec, map_neg] at hv
    simpa [Fintype.linearCombination_apply] using congrArg Additive.toMul hv

end Matrix.SpecialLinearGroup.PrimePlaneAction
