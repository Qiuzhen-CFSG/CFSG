module
public import Theory.SpecificGroups.SL2.ThreeCubicCentralizer

/-!
# A cubic inverted by an outer involution of SL₂(3)

Lift an automorphism to GL₂(3). Outerness forces determinant minus one;
involutivity makes its square commute with both generating unipotents.
A kernel-checked calculation on the 81 two-by-two matrices over ZMod 3
then produces an inverted nonidentity cubic. Transport preserves the
given SL₂(3) marking and the actual automorphism.

This supplies the common torus in `G2Recognition.CubicTorus`, following
Fong–Wong, Nagoya Math. J.36 (1969), §3, equations (3.1)–(3.2), p.155.
-/

public section
open Matrix Subgroup
namespace Matrix.SpecialLinearGroup
local notation "SL23" => SpecialLinearGroup (Fin 2) (ZMod 3)
private abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 3)
private theorem cubic_inverted_matrix : ∀ A : Mat, A.det ≠ 0 → A.det ≠ 1 →
    A^2 * GeneralLinearGroup.threeUnipotent.val = GeneralLinearGroup.threeUnipotent.val * A^2 →
    A^2 * GeneralLinearGroup.threeLower.val = GeneralLinearGroup.threeLower.val * A^2 →
    ∃ B : Mat, B.det=1 ∧ B^3=1 ∧ B≠1 ∧ A*B=B^2*A := by
  decide +kernel

theorem involutive_outer_inverts_cubic_of_equiv {I : Type*} [Group I]
    (e : I ≃* SL23) (a : MulAut I) (ha : Function.Involutive a)
    (hout : ∀ y : I, a ≠ MulAut.conj y) :
    ∃ x : I, orderOf x = 3 ∧ a x = x⁻¹ := by
  let eK := e.trans GeneralLinearGroup.threeSpecialLinearEquiv.symm
  let b := (MulAut.congr eK) a
  obtain ⟨g,hg⟩ := GeneralLinearGroup.three_specialLinear_aut_surjective b
  have hgg (t : GeneralLinearGroup.threeSpecialLinear) :
      (MulAut.conjNormal g : MulAut GeneralLinearGroup.threeSpecialLinear)
        ((MulAut.conjNormal g) t) = t := by
    rw [hg]
    change eK (a (eK.symm (eK (a (eK.symm t))))) = t
    rw [eK.symm_apply_apply,ha,eK.apply_symm_apply]
  have hdet : g.val.det ≠ 1 := by
    intro hd
    have hgK : g ∈ GeneralLinearGroup.threeSpecialLinear :=
      (GeneralLinearGroup.three_mem_specialLinear g).mpr hd
    apply hout (eK.symm ⟨g,hgK⟩)
    apply MulEquiv.ext
    intro t
    apply eK.injective
    have hh := congrArg (fun f : MulAut GeneralLinearGroup.threeSpecialLinear => f (eK t)) hg
    have hh' : eK (a t) = (MulAut.conjNormal g) (eK t) := by
      simpa [b,MulAut.congr_apply] using hh.symm
    rw [hh']
    apply Subtype.ext
    simp only [MulAut.conj_apply,map_mul,map_inv,eK.apply_symm_apply]
    rfl
  have hcomm (t : GeneralLinearGroup.threeSpecialLinear) :
      g.val^2 * t.val.val = t.val.val * g.val^2 := by
    have hh := congrArg Subtype.val (hgg t)
    change g*(g*t.val*g⁻¹)*g⁻¹=t.val at hh
    have he : g^2*t.val*(g^2)⁻¹=t.val := by
      calc
        _ = g*(g*t.val*g⁻¹)*g⁻¹ := by simp only [pow_two]; group
        _ = t.val := hh
    exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp he)
  obtain ⟨B,hBdet,hB3,hBne,hAB⟩ := cubic_inverted_matrix g.val g.det_ne_zero hdet
    (hcomm ⟨GeneralLinearGroup.threeUnipotent,
      GeneralLinearGroup.three_cubic_mem_specialLinear _ (by decide +kernel)⟩)
    (hcomm ⟨GeneralLinearGroup.threeLower,
      GeneralLinearGroup.three_cubic_mem_specialLinear _ (by decide +kernel)⟩)
  let v : GeneralLinearGroup.threeSpecialLinear :=
    ⟨GeneralLinearGroup.mkOfDetNeZero B (by rw [hBdet]; decide),
      (GeneralLinearGroup.three_mem_specialLinear _).mpr hBdet⟩
  let x : I := eK.symm v
  have hv3 : v^3=1 := Subtype.ext (Units.ext hB3)
  have hvne : v≠1 := fun hh => hBne (congrArg (fun w : GeneralLinearGroup.threeSpecialLinear => w.val.val) hh)
  have hx3 : orderOf x=3 := (eK.symm.orderOf_eq v).trans (orderOf_eq_prime hv3 hvne)
  refine ⟨x,hx3,?_⟩
  apply eK.injective
  have hh := congrArg (fun f : MulAut GeneralLinearGroup.threeSpecialLinear => f (eK x)) hg
  have hex : eK x = v := eK.apply_symm_apply v
  have he : (MulAut.conjNormal g : MulAut GeneralLinearGroup.threeSpecialLinear) (eK x) = (eK x)^2 := by
    rw [hex]
    apply Subtype.ext
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Units.ext hAB
  have hx2 : x^2=x⁻¹ := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel,←pow_succ',show x^3=1 by simpa only [hx3] using pow_orderOf_eq_one x]
  calc
    eK (a x) = (MulAut.conjNormal g) (eK x) := by
      simpa [b,MulAut.congr_apply] using hh.symm
    _ = (eK x)^2 := he
    _ = eK (x⁻¹) := by rw [←map_pow,hx2]
end Matrix.SpecialLinearGroup
