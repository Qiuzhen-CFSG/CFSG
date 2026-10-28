module
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong.RootSeparation
import all Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy

/-!
# Long-root equations in the actual six-root Sylow subgroup

The involution normal forms together with the octonion-unit obstruction to
short/long conjugacy force a long element with coordinates `(a,b,c,d,e,f)`
to satisfy `f=0`, `d²=ec`, `c²=bd`, and `be=cd`. These equations are proved
over every finite field of characteristic two, including the binary field.

The `import all` is an intentional internal extension of the same involution
geometry family: it reuses the established E/F/D conjugation formulas and
square-coordinate calculation without changing their existing public boundary.
Source: Aschbacher–Smith B.4.6(11), printed p.89. The root formulas are the
licensed ATLAS G₂ development imported by `InvolutionConjugacy`.
-/

namespace Atlas.G2.EvenInvolutionGeometry.PureLong
open LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

private theorem ABC_long_c_zero (a b c : F)
    (hl : ShortRootProducts.IsLongRootElement (unipotentProduct ![a,b,c,0,0,0])) : c = 0 := by
  by_contra hc
  have he : unipotentProduct ![a,b,c,0,0,0] =
      MulAut.conj (rootF (b/c) * rootD (a/c)) (rootC c) := by
    rw [map_mul, MulAut.mul_apply]
    have hC : rootC c = unipotentProduct ![0,0,c,0,0,0] := by simp [unipotentProduct]
    rw [hC, conjugate_D, conjugate_F]
    simp [mul_div_cancel₀ _ hc]
  exact rootC_not_long hc (long_of_conj _ (he ▸ hl))

private theorem five_nonzero_E_long [Finite F] (a b c d e : F) (he : e ≠ 0)
    (hl : ShortRootProducts.IsLongRootElement (unipotentProduct ![a,b,c,d,e,0])) :
    d ^ 2 = e * c := by
  obtain ⟨z,hz⟩ := isSquare_of_charTwo' (c/e)
  have hz' : e*z^2 = c := by
    rw [pow_two, ← hz, mul_div_cancel₀ _ he]
  let a' := a+d^2*z+d*e*z^2+e^2*z^3
  let b' := b+c*z+d*z^2+e*z^3
  let d' := d+e*z
  have hconj : MulAut.conj (rootF z) (unipotentProduct ![a,b,c,d,e,0]) =
      unipotentProduct ![a',b',0,d',e,0] := by
    rw [conjugate_F, hz', CharTwo.add_self_eq_zero]
  have hl' : ShortRootProducts.IsLongRootElement (unipotentProduct ![a',b',0,d',e,0]) :=
    hconj ▸ long_conj (rootF z) hl
  have hb : b'=0 := by
    have hh := five_relation a' b' 0 d' e (long_pow_two hl')
    simpa using (mul_eq_zero.mp (by simpa using hh : b'*e=0)).resolve_right he
  have hw : MulAut.conj weylS (unipotentProduct ![a',b',0,d',e,0]) =
      unipotentProduct ![a',e,d',0,0,0] := by
    change weylS * _ * weylS⁻¹ = _
    rw [weylS_fiveRoot_conjugate _ rfl]
    simp [hb]
  have hd' : d' = 0 := ABC_long_c_zero _ _ _ (hw ▸ long_conj weylS hl')
  have hd : d = e*z := by
    have hh : d + e*z = 0 := hd'
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  calc
    d ^ 2 = (e*z)^2 := by rw [hd]
    _ = e*(e*z^2) := by ring
    _ = e*c := by rw [hz']

private theorem five_zero_E_long [Finite F] (a b c d : F)
    (hl : ShortRootProducts.IsLongRootElement (unipotentProduct ![a,b,c,d,0,0])) :
    c = 0 ∧ d = 0 := by
  have hcd : c*d = 0 := by simpa using five_relation a b c d 0 (long_pow_two hl)
  rcases mul_eq_zero.mp hcd with hc | hd
  · subst c
    have hw : MulAut.conj weylS (unipotentProduct ![a,b,0,d,0,0]) =
        unipotentProduct ![a,0,d,0,b,0] := by
      change weylS * _ * weylS⁻¹ = _
      rw [weylS_fiveRoot_conjugate _ rfl]
      simp
    have hl' : ShortRootProducts.IsLongRootElement (unipotentProduct ![a,0,d,0,b,0]) :=
      hw ▸ long_conj weylS hl
    refine ⟨rfl, ?_⟩
    by_cases hb : b = 0
    · subst b
      exact ABC_long_c_zero _ _ _ hl'
    · have hh := five_nonzero_E_long a 0 d 0 b hb hl'
      have hh' : b*d = 0 := by simpa using hh.symm
      exact (mul_eq_zero.mp hh').resolve_left hb
  · subst d
    exact ⟨ABC_long_c_zero _ _ _ hl, rfl⟩

private theorem five_long_equations [Finite F] (a b c d e : F)
    (hl : ShortRootProducts.IsLongRootElement (unipotentProduct ![a,b,c,d,e,0])) :
    d^2 = e*c ∧ c^2 = b*d ∧ b*e = c*d := by
  have hbe : b*e = c*d := by
    have hh := five_relation a b c d e (long_pow_two hl)
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  by_cases he : e = 0
  · subst e
    obtain ⟨hc,hd⟩ := five_zero_E_long a b c d hl
    simp [hc,hd]
  · have hd := five_nonzero_E_long a b c d e he hl
    refine ⟨hd, ?_, hbe⟩
    apply mul_left_cancel₀ he
    calc
      e*c^2 = c*(e*c) := by ring
      _ = c*d^2 := by rw [← hd]
      _ = (c*d)*d := by ring
      _ = (b*e)*d := by rw [← hbe]
      _ = e*(b*d) := by ring

private theorem long_sixth_zero [Finite F] (t : Fin 6 → F)
    (hl : ShortRootProducts.IsLongRootElement (unipotentProduct t)) : t 5 = 0 := by
  by_contra hf
  have ht : t = ![t 0,t 1,t 2,t 3,t 4,t 5] := by ext i; fin_cases i <;> rfl
  have hs := square_zero t (long_pow_two hl)
  have hef : t 4 * t 5 = 0 := by simpa [square_parameters] using congrFun hs 3
  have he : t 4 = 0 := (mul_eq_zero.mp hef).resolve_right hf
  have hcf : (t 2 + t 3*t 5)*t 5 = 0 := by
    have hh := congrFun hs 1
    simp only [square_parameters, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.zero_apply, he, zero_mul, add_zero] at hh
    linear_combination hh
  have hc : t 2 = t 3*t 5 := by
    have hh := (mul_eq_zero.mp hcf).resolve_right hf
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  have hd : t 5 * (t 3 / t 5) = t 3 := by field_simp
  have hcc : (t 5)^2 * (t 3/t 5) = t 3*t 5 := by
    rw [pow_two, mul_assoc, hd, mul_comm]
  let a := t 0 + t 1*(t 3/t 5) + t 3*(t 5)^2*(t 3/t 5)
  let b := t 1 + (t 5)^3*(t 3/t 5)
  have hE : MulAut.conj (rootE (t 3/t 5)) (unipotentProduct t) =
      unipotentProduct ![a,b,0,0,0,t 5] := by
    rw [show unipotentProduct t = unipotentProduct ![t 0,t 1,t 2,t 3,t 4,t 5] from
      congrArg unipotentProduct ht, conjugate_E]
    simp only [he, zero_mul, add_zero, hd, hcc, hc, CharTwo.add_self_eq_zero]
    rfl
  have hR := conjugate_R_ABF a b (t 5)
  have hl' : ShortRootProducts.IsLongRootElement (unipotentProduct ![b,a,0,t 5,0,0]) :=
    hR ▸ long_conj weylR (hE ▸ long_conj (rootE (t 3/t 5)) hl)
  exact hf (five_zero_E_long b a 0 (t 5) hl').2

public theorem unipotent_long_coordinates [Finite F] (t : Fin 6 → F)
    (hl : ShortRootProducts.IsLongRootElement (unipotentProduct t)) :
    t 5 = 0 ∧ (t 3)^2 = t 4*t 2 ∧ (t 2)^2 = t 1*t 3 ∧ t 1*t 4 = t 2*t 3 := by
  have hf := long_sixth_zero t hl
  have ht : t = ![t 0,t 1,t 2,t 3,t 4,0] := by ext i; fin_cases i <;> simp [hf]
  refine ⟨hf, ?_⟩
  exact five_long_equations _ _ _ _ _ (ht ▸ hl)

public theorem unipotent_one_or_long_coordinates [Finite F] (t : Fin 6 → F)
    (hl : unipotentProduct t = 1 ∨ ShortRootProducts.IsLongRootElement (unipotentProduct t)) :
    t 5 = 0 ∧ (t 3)^2 = t 4*t 2 ∧ (t 2)^2 = t 1*t 3 ∧ t 1*t 4 = t 2*t 3 := by
  rcases hl with hl | hl
  · have ht : t = 0 := unipotentProduct_injective (hl.trans unipotentProduct_zero.symm)
    simp [ht]
  · exact unipotent_long_coordinates t hl

end Atlas.G2.EvenInvolutionGeometry.PureLong
