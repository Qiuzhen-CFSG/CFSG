module
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Projection
/-!
# Determinants in the terminal Cartan calculation

Two scalar planes have determinant a²b². In characteristic two,
determinant one forces a=b⁻¹. A complementary invariant line to a
b⁻¹-plane in a determinant-one three-space then has weight b².
The source applications, with the actual compatible field and conjugation
representations, are in TerminalWeights.Source.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
section Linear
variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [Module.Finite F M]
private theorem det_of_scalar_complements (t : Module.End F M) (U W : Submodule F M)
    (hc : IsCompl U W) (a b : F)
    (hU : ∀ u ∈ U, t u = a • u) (hW : ∀ w ∈ W, t w = b • w) :
    t.det = a ^ Module.finrank F U * b ^ Module.finrank F W := by
  let e := Submodule.prodEquivOfIsCompl U W hc
  have he : e.symm.toLinearMap ∘ₗ t ∘ₗ e.toLinearMap =
      LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id) := by
    apply LinearMap.ext
    rintro ⟨u,w⟩
    apply e.injective
    change e (e.symm (t (e (u,w)))) = e (a • u,b • w)
    rw [e.apply_symm_apply]
    change t (u.val + w.val) = a • u.val + b • w.val
    rw [map_add,hU u.val u.property,hW w.val w.property]
  have hd := congrArg LinearMap.det he
  have hdc := LinearMap.det_conj t e.symm
  simp only [LinearEquiv.symm_symm] at hdc
  rw [hdc] at hd
  simpa only [LinearMap.det_prodMap,LinearMap.det_smul,LinearMap.det_id,mul_one] using hd

omit [Module.Finite F M] in
private theorem scalar_on_line (t : Module.End F M) (W : Submodule F M)
    (hdim : Module.finrank F W = 1) (hi : ∀ w ∈ W, t w ∈ W) :
    ∃ b : F, ∀ w ∈ W, t w = b • w := by
  let s : Module.End F W := t.restrict hi
  obtain ⟨b,hb,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim s
  refine ⟨b,fun w hw => ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hb ⟨w,hw⟩)

theorem inverse_plane_weight [CharP F 2] (t : Module.End F M)
    (U W : Submodule F M) (hc : IsCompl U W)
    (hdU : Module.finrank F U = 2) (hdW : Module.finrank F W = 2)
    (hdet : t.det = 1) (a b : F)
    (hU : ∀ u ∈ U, t u = a • u) (hW : ∀ w ∈ W, t w = b • w) : a = b⁻¹ := by
  have hd := det_of_scalar_complements t U W hc a b hU hW
  rw [hdU,hdW,hdet,←mul_pow] at hd
  have hab : a*b=1 := CharTwo.sq_injective (hd.symm.trans (one_pow 2).symm)
  exact eq_inv_of_mul_eq_one_left hab

theorem square_line_weight (t : Module.End F M)
    (U W : Submodule F M) (hc : IsCompl U W)
    (hdU : Module.finrank F U = 2) (hdW : Module.finrank F W = 1)
    (hdet : t.det = 1) (a : F) (ha : a ≠ 0)
    (hU : ∀ u ∈ U, t u = a⁻¹ • u) (hi : ∀ w ∈ W, t w ∈ W) :
    ∀ w ∈ W, t w = a^2 • w := by
  obtain ⟨b,hb⟩ := scalar_on_line t W hdW hi
  have hd := det_of_scalar_complements t U W hc a⁻¹ b hU hb
  rw [hdU,hdW,hdet,pow_one,inv_pow] at hd
  have he : b = a^2 := by
    have hh := congrArg (fun z : F => a^2*z) hd
    simpa [←mul_assoc,ha] using hh.symm
  simpa [he] using hb
end Linear
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
