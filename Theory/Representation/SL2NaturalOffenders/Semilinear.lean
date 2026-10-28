module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Card

/-!
# Semilinearity of normalizers of the natural SL₂ action

Commutation with upper and lower transvections makes every additive
endomorphism in the centralizer a field scalar. Conjugating these scalars by
an ambient actor therefore constructs a field endomorphism. Finiteness makes
it an automorphism, giving the actual semilinearity equation.

This is the normalizer step in the natural-module offender calculation of
Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), B.4.2(1), printed p.86. It uses the specified matrix action and
normality, without an automorphism classification or an innerness premise.
-/

public section

namespace Representation.SL2NaturalOffenders
open Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

/-- An additive endomorphism commuting with natural SL₂ is multiplication by
a field scalar. Upper and lower transvections determine both coordinate axes. -/
theorem centralizer_scalar (f : (Fin 2 → F) →+ (Fin 2 → F))
    (hf : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      f (g.val.mulVec v) = g.val.mulVec (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  have hx (t : F) : f ![t, 0] = ![t * f ![0, 1] 1, 0] := by
    have h := hf (transvection (i := 0) (j := 1) zero_ne_one t) ![0, 1]
    have he : (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t :
        Matrix.SpecialLinearGroup (Fin 2) F).val.mulVec ![0, 1] = ![t, 0] + ![0, 1] := by
      ext i
      fin_cases i <;> simp [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [he, map_add] at h
    ext i
    fin_cases i
    · have hh := congrFun h 0
      simp [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh ⊢
      exact add_right_cancel (hh.trans (add_comm _ _))
    · have hh := congrFun h 1
      simpa [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh
  have hy (t : F) : f ![0, t] = ![0, t * f ![1, 0] 0] := by
    have h := hf (transvection (i := 1) (j := 0) one_ne_zero t) ![1, 0]
    have he : (transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t :
        Matrix.SpecialLinearGroup (Fin 2) F).val.mulVec ![1, 0] = ![0, t] + ![1, 0] := by
      ext i
      fin_cases i <;> simp [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [he, map_add] at h
    ext i
    fin_cases i
    · have hh := congrFun h 0
      simpa [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh
    · have hh := congrFun h 1
      simp [transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh ⊢
      exact hh
  refine ⟨f ![0, 1] 1, fun v => ?_⟩
  have he : v = ![v 0, 0] + ![0, v 1] := by ext i; fin_cases i <;> simp
  have hc : f ![1, 0] 0 = f ![0, 1] 1 := by simpa using congrFun (hx 1) 0
  calc
    f v = f ![v 0, 0] + f ![0, v 1] := (congrArg f he).trans (f.map_add _ _)
    _ = ![v 0 * f ![0, 1] 1, 0] + ![0, v 1 * f ![1, 0] 0] :=
      congrArg₂ (· + ·) (hx (v 0)) (hy (v 1))
    _ = f ![0, 1] 1 • v := by ext i; fin_cases i <;> simp [hc, mul_comm]
end Representation.SL2NaturalOffenders


namespace Representation.SL2NaturalOffenders
open Matrix.SpecialLinearGroup
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- Normality of the natural SL₂ layer forces the ambient binary action to be
semilinear over the matrix field. No faithfulness assumption is needed here. -/
theorem normalizer_semilinear (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (h : H) : ∃ σ : F ≃+* F, ∀ (c : F) (v : Fin 2 → F),
      ρ h (c • v) = σ c • ρ h v := by
  let f (c : F) : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => ρ h (c • ρ h⁻¹ v)
      map_zero' := by simp
      map_add' := by intro v w; simp [smul_add] }
  have hf (c : F) : ∃ d : F, ∀ v, f c v = d • v := by
    apply centralizer_scalar
    intro g v
    let x : L := e.symm g
    let y : L := ⟨h⁻¹ * (x : H) * h, (inferInstance : L.Normal).conj_mem' x x.property h⟩
    have hx (v : Fin 2 → F) : g.val.mulVec v = ρ (x : H) v := by
      rw [hnat]
      simp [x]
    have hy (c : F) (v : Fin 2 → F) : ρ (y : H) (c • v) = c • ρ (y : H) v := by
      simp only [hnat, Matrix.mulVec_smul]
    have hy₁ (v : Fin 2 → F) : ρ h⁻¹ (ρ (x : H) v) = ρ (y : H) (ρ h⁻¹ v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel, mul_one]
    have hy₂ (v : Fin 2 → F) : ρ h (ρ (y : H) v) = ρ (x : H) (ρ h v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel_left]
    change ρ h (c • ρ h⁻¹ (g.val.mulVec v)) = g.val.mulVec (ρ h (c • ρ h⁻¹ v))
    rw [hx, hx, hy₁, ← hy, hy₂]
  let φ : F → F := fun c => (f c ![1, 0]) 0
  have hφ (c : F) (v : Fin 2 → F) : f c v = φ c • v := by
    obtain ⟨d, hd⟩ := hf c
    have he : φ c = d := by simp [φ, hd]
    exact he ▸ hd v
  have hcancel (v : Fin 2 → F) : ρ h (ρ h⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hcancel' (v : Fin 2 → F) : ρ h⁻¹ (ρ h v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hmul (a b : F) (v : Fin 2 → F) : f (a * b) v = f a (f b v) := by
    simp [f, hcancel', mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, f, hcancel]
      map_mul' := by
        intro a b
        change (f (a * b) ![1, 0]) 0 = φ a * φ b
        rw [hmul, hφ, hφ]
        simp
      map_zero' := by simp [φ, f]
      map_add' := by intro a b; simp [φ, f, add_smul] }
  have hbij : Function.Bijective φhom :=
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩
  refine ⟨RingEquiv.ofBijective φhom hbij, fun c v => ?_⟩
  have he := hφ c (ρ h v)
  simpa only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hcancel',
    RingEquiv.ofBijective_apply, φhom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using he
end Representation.SL2NaturalOffenders
