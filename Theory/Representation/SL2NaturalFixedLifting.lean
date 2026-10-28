module

public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.ZMod

/-!
# Fixed-point lifting for central extensions of the natural SL₂-module

Over a characteristic-two field, a nonidentity determinant-one matrix fixing
a nonzero vector is unipotent. In coordinates beginning with that vector, it
is an upper transvection: its square is one, and the fixed vector is a
displacement. Lift the displaced vector through an equivariant surjection.
The lifted displacement is fixed because the source is a binary module;
the difference from the original vector lies in the fixed kernel.

This proves the rank-one fixed-lifting consequence of Aschbacher–Smith,
combined manuscript (1 March 2004), I.2.3(1), printed p.413/PDF p.424,
used in C.5.6 (*), printed p.156/PDF p.167. It preserves arbitrary central
layers and does not require the classification of universal covers.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Representation.SL2NaturalFixedLifting
variable {F : Type*} [Field F] [CharP F 2]

private theorem fixed_nonzero (g : SL(2,F)) (hg : g ≠ 1)
    (v : Fin 2 → F) (hv : v ≠ 0) (hfix : g • v = v) :
    g * g = 1 ∧ ∃ w : Fin 2 → F, g • w - w = v := by
  obtain ⟨b, hb⟩ := Matrix.SL2.exists_mulVec_eq F ![1,0] v
    (by intro h; have := congrFun h 0; simp at this) hv
  change b • (![1,0] : Fin 2 → F) = v at hb
  let c := MulAut.conj b⁻¹
  let t := c g
  have htfix : t • (![1,0] : Fin 2 → F) = ![1,0] := by
    change (b⁻¹ * g * (b⁻¹)⁻¹) • _ = _
    rw [inv_inv, mul_smul, mul_smul, hb, hfix, ← hb, inv_smul_smul]
  have h00 : t.val 0 0 = 1 := by
    have he := congrFun htfix 0
    change (t.val *ᵥ ![1,0]) 0 = 1 at he
    simp only [mulVec, dotProduct, Fin.sum_univ_two] at he
    dsimp at he
    simpa only [mul_one, mul_zero, add_zero] using he
  have h10 : t.val 1 0 = 0 := by
    have he := congrFun htfix 1
    change (t.val *ᵥ ![1,0]) 1 = 0 at he
    simp only [mulVec, dotProduct, Fin.sum_univ_two] at he
    dsimp at he
    simpa only [mul_one, mul_zero, add_zero] using he
  have h11 : t.val 1 1 = 1 := by
    have hd : t.val.det = 1 := t.property
    rw [det_fin_two, h00, h10] at hd
    simpa only [one_mul, mul_zero, sub_zero] using hd
  have ht : t.val = !![1, t.val 0 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00,h10,h11]
  have ht2 : t * t = 1 := by
    apply Subtype.ext
    change t.val * t.val = 1
    rw [ht]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have ht01 : t.val 0 1 ≠ 0 := by
    intro hz
    have ht1 : t = 1 := by
      apply Subtype.ext
      rw [ht, hz]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    exact hg (c.injective (ht1.trans c.map_one.symm))
  have hw : t • (![0, (t.val 0 1)⁻¹] : Fin 2 → F) - ![0, (t.val 0 1)⁻¹] = ![1,0] := by
    change t.val *ᵥ _ - _ = _
    rw [ht]
    ext i; fin_cases i <;>
      simp [ht01]
  refine ⟨c.injective (by simpa only [map_mul, map_one] using ht2),
    b • (![0, (t.val 0 1)⁻¹] : Fin 2 → F), ?_⟩
  rw [← hb, ← hw, smul_sub]
  congr 1
  change g • (b • _) = b • ((b⁻¹ * g * (b⁻¹)⁻¹) • _)
  simp only [inv_inv, mul_smul, smul_inv_smul]

end Representation.SL2NaturalFixedLifting

namespace Representation.SL2NaturalFixedLifting
open Representation
variable {F W : Type*} [Field F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Quotient fixed vectors lift through a central extension of the natural binary
SL₂-module. No vanishing of the fixed kernel, finiteness, or universal-cover
identification is required. -/
theorem fixed_lift_of_fixed_kernel (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W)
    (p : W →+ (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (σ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, σ g w = w)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : W)
    (hv : p (σ g v) = p v) : σ g v = v := by
  by_cases hg : g = 1
  · subst g
    simp
  by_cases hz : p v = 0
  · exact hk v hz g
  have hfix : g • p v = p v := (he g v).symm.trans hv
  obtain ⟨hgg, w, hw⟩ := fixed_nonzero g hg (p v) hz hfix
  obtain ⟨u, hu⟩ := hp w
  have hn (x : W) : -x = x := by
    apply neg_eq_iff_add_eq_zero.mpr
    calc x + x = (1 + 1 : ZMod 2) • x := by rw [add_smul, one_smul]
         _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from rfl, zero_smul]
  have huu : σ g (σ g u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, hgg, map_one, Module.End.one_apply]
  have hd : σ g (σ g u - u) = σ g u - u := by
    rw [map_sub, huu]
    simp only [sub_eq_add_neg, hn, add_comm]
  have hz' : p (v - (σ g u - u)) = 0 := by
    rw [map_sub, map_sub, he, hu, hw, sub_self]
  have h := hk _ hz' g
  rw [map_sub, hd] at h
  exact sub_left_inj.mp h
end Representation.SL2NaturalFixedLifting


end
