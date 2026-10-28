module
public import Theory.SpecificGroups.HeisenbergPrime.ScalarAction
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic

/-!
# The ternary Heisenberg outer action

The two noncentral coordinates give the literal homomorphism from automorphisms
of the order-27 Heisenberg group to GL₂(3). Its kernel is exactly the inner
automorphisms. The determinant-one preimage consists exactly of automorphisms
fixing the center. Both statements transport along a supplied group isomorphism.

The coordinate checks range only over 27 triples; the automorphism transport
and kernel comparison are structural. This retains the inner kernel in the
normalizer argument of Aschbacher–Smith 14.7.21, printed p.1049.
-/

public noncomputable section
open Subgroup Matrix
namespace HeisenbergPrime.TernaryOuterAction
abbrev P := HeisenbergPrime 3
private def x : P := ⟨1,0,0⟩
private def y : P := ⟨0,1,0⟩
private def z (c : ZMod 3) : P := ⟨0,0,c⟩
private theorem coordinates_product : ∀ v : P,
    v = x ^ v.a.val * y ^ v.b.val * z (v.c - v.a*v.b) := by
  intro ⟨a,b,c⟩
  apply HeisenbergPrime.ext <;> revert a b c <;> decide +kernel
private theorem action_coordinates (α : MulAut P) (v : P) :
    (α v).a = (α x).a * v.a + (α y).a * v.b ∧
    (α v).b = (α x).b * v.a + (α y).b * v.b := by
  have hz (c : ZMod 3) : (α (z c)).a = 0 ∧ (α (z c)).b = 0 := by
    apply (HeisenbergPrime.mem_center_iff _).mp
    exact ((MulAut.characteristic (center P) α)
      ⟨z c,(HeisenbergPrime.mem_center_iff _).mpr ⟨rfl,rfl⟩⟩).property
  have he := congrArg α (coordinates_product v)
  rw [map_mul,map_mul,map_pow,map_pow] at he
  constructor
  · rw [he]
    simp only [mul_a,pow_a,hz,ZMod.natCast_zmod_val,add_zero]
    ring
  · rw [he]
    simp only [mul_b,pow_b,hz,ZMod.natCast_zmod_val,add_zero]
    ring

private def mat (α : MulAut P) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![(α x).a, (α y).a; (α x).b, (α y).b]

private theorem mat_mul (α β : MulAut P) : mat (α * β) = mat α * mat β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,MulAut.mul_apply]
  · exact (action_coordinates α (β x)).1
  · exact (action_coordinates α (β y)).1
  · exact (action_coordinates α (β x)).2
  · exact (action_coordinates α (β y)).2

private theorem mat_one : mat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The original automorphism's action on the two noncentral coordinates. -/
def action : MulAut P →* GL (Fin 2) (ZMod 3) where
  toFun α := ⟨mat α,mat α⁻¹,by rw [←mat_mul,mul_inv_cancel,mat_one],
    by rw [←mat_mul,inv_mul_cancel,mat_one]⟩
  map_one' := Units.ext mat_one
  map_mul' α β := Units.ext (mat_mul α β)

theorem action_ker : action.ker = MulAut.innerSubgroup P := by
  let : IsExtraspecial 3 P := HeisenbergPrime.isExtraspecial (by decide)
  rw [show MulAut.innerSubgroup P = (quotientAut (center P)).ker from
    (IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 3)).symm]
  ext α
  constructor
  · intro ha
    have hm : mat α = 1 := congrArg Units.val ha
    have hx : (α x).a = 1 ∧ (α x).b = 0 :=
      ⟨congrArg (fun m => m 0 0) hm,congrArg (fun m => m 1 0) hm⟩
    have hy : (α y).a = 0 ∧ (α y).b = 1 :=
      ⟨congrArg (fun m => m 0 1) hm,congrArg (fun m => m 1 1) hm⟩
    apply MulEquiv.ext
    intro v
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (HeisenbergPrime.mem_center_iff _).mpr
    have hv := action_coordinates α v
    simp only [hx.1,hx.2,hy.1,hy.2,one_mul,zero_mul,add_zero,zero_add] at hv
    simpa only [div_eq_mul_inv,mul_a,mul_b,inv_a,inv_b,add_neg_eq_zero] using hv
  · intro ha
    have hab (v : P) : (α v).a = v.a ∧ (α v).b = v.b := by
      have he := DFunLike.congr_fun ha (QuotientGroup.mk' (center P) v)
      rw [quotientAut_apply_mk] at he
      have hc := (HeisenbergPrime.mem_center_iff _).mp (QuotientGroup.eq_iff_div_mem.mp he)
      simpa only [div_eq_mul_inv,mul_a,mul_b,inv_a,inv_b,add_neg_eq_zero] using hc
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact (hab x).1
    · exact (hab y).1
    · exact (hab x).2
    · exact (hab y).2

theorem action_mem_special_iff (α : MulAut P) :
    action α ∈ GeneralLinearGroup.threeSpecialLinear ↔
      ∀ v ∈ center P, α v = v := by
  rw [GeneralLinearGroup.three_mem_specialLinear]
  change (mat α).det = 1 ↔ _
  have hd (v : P) (hv : v ∈ center P) := center_coordinate_determinant
    (MulEquiv.refl P) α (α x).a (α y).a (α x).b (α y).b
    (fun w => (action_coordinates α w).1) (fun w => (action_coordinates α w).2) v hv
  have hdet : (mat α).det = (α x).a * (α y).b - (α y).a * (α x).b := by
    simp [mat,Matrix.det_fin_two,mul_comm]
  rw [hdet]
  constructor
  · intro hh v hv
    have hb := (HeisenbergPrime.mem_center_iff _).mp
      ((MulAut.characteristic (center P) α) ⟨v,hv⟩).property
    have hvb := (HeisenbergPrime.mem_center_iff _).mp hv
    exact HeisenbergPrime.ext (hb.1.trans hvb.1.symm) (hb.2.trans hvb.2.symm)
      (by simpa only [MulEquiv.refl_apply,hh,one_mul] using hd v hv)
  · intro hh
    have hz : z 1 ∈ center P := (HeisenbergPrime.mem_center_iff _).mpr ⟨rfl,rfl⟩
    have he := hd (z 1) hz
    simpa only [MulEquiv.refl_apply,hh _ hz,show (z 1).c = 1 from rfl,mul_one] using he.symm

variable {Q : Type*} [Group Q]

/-- The same plane action through the supplied marking of the original group. -/
def markedAction (e : Q ≃* P) : MulAut Q →* GL (Fin 2) (ZMod 3) :=
  action.comp (MulAut.congr e).toMonoidHom

/-- Changing coordinates preserves the full inner-automorphism kernel. -/
theorem markedAction_ker (e : Q ≃* P) :
    (markedAction e).ker = MulAut.innerSubgroup Q := by
  rw [markedAction,←MonoidHom.comap_ker,action_ker,←MulAut.map_innerSubgroup_congr e]
  exact comap_map_eq_self_of_injective (MulAut.congr e).injective _

/-- The determinant-one condition retains pointwise centralization of the original center. -/
theorem markedAction_mem_special_iff (e : Q ≃* P) (α : MulAut Q) :
    markedAction e α ∈ GeneralLinearGroup.threeSpecialLinear ↔
      ∀ v ∈ center Q, α v = v := by
  rw [markedAction,MonoidHom.comp_apply,action_mem_special_iff]
  constructor
  · intro hh v hv
    have he := hh (e v) ((centerCongr e ⟨v,hv⟩).property)
    apply e.injective
    change e (α (e.symm (e v))) = e v at he
    simpa only [MulEquiv.symm_apply_apply] using he
  · intro hh v hv
    have he := hh (e.symm v) ((centerCongr e.symm ⟨v,hv⟩).property)
    change e (α (e.symm v)) = v
    rw [he,MulEquiv.apply_symm_apply]

end HeisenbergPrime.TernaryOuterAction
