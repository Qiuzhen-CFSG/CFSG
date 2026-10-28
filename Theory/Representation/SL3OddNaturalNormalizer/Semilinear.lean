module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Card

/-!
# Semilinearity of the natural SL₃ normalizer

Elementary transvections force each additive map commuting with the natural
SL₃ action to be a field scalar. Conjugation by a normalizing binary operator
therefore induces a unique field automorphism. These automorphisms form a
homomorphism, whose kernel acts linearly over the original field.

This is the intrinsic natural-module input to Aschbacher–Smith, *The
Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
B.5.9(4) and B.5.10(2), printed pp.107–109. The argument works over F₂ as
well. It adapts the scalar calculation in `SL3FourNaturalDual` and the
normalizer argument in `SL2NaturalOffenders` to arbitrary finite fields.
-/

public section
namespace Representation.SL3OddNaturalNormalizer
open Matrix
variable {F : Type*} [Field F]

private lemma natural_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) (v : Fin 3 → F) :
    (specialLinearNatural 3) (SpecialLinearGroup.transvection hij a) v =
      v + Pi.single i (a * v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

theorem centralizer_scalar (f : (Fin 3 → F) →+ (Fin 3 → F))
    (hf : ∀ (g : SpecialLinearGroup (Fin 3) F) v, f (specialLinearNatural 3 g v) = specialLinearNatural 3 g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  have hsingle {i j : Fin 3} (hij : i ≠ j) (a : F) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single j 1) j) := by
    have h := hf (SpecialLinearGroup.transvection hij a) (Pi.single j 1)
    rw [natural_transvection, natural_transvection, map_add] at h
    simpa using add_left_cancel h
  have hdiag {i j : Fin 3} (hij : i ≠ j) :
      f (Pi.single i 1) i = f (Pi.single j 1) j := by
    simpa using congrFun (hsingle hij 1) i
  have hs (i : Fin 3) (a : F) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single 0 1) 0) := by
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide
    rw [hsingle hij]
    by_cases hj : j = 0
    · rw [hj]
    · rw [hdiag hj]
  refine ⟨f (Pi.single 0 1) 0, fun v => ?_⟩
  have hv : v = ∑ i : Fin 3, Pi.single i (v i) := by
    funext i
    simp [Finset.sum_apply]
  calc
    f v = ∑ i : Fin 3, f (Pi.single i (v i)) := by rw [← map_sum, ← hv]
    _ = ∑ i : Fin 3, Pi.single i (v i * f (Pi.single 0 1) 0) :=
      Finset.sum_congr rfl (fun i _ => hs i (v i))
    _ = f (Pi.single 0 1) 0 • v := by
      funext i
      simp [Finset.sum_apply, mul_comm]

end Representation.SL3OddNaturalNormalizer

namespace Representation.SL3OddNaturalNormalizer
open Matrix.SpecialLinearGroup
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- Normality of the natural SL₃ layer forces the ambient binary action to be
semilinear over the matrix field. No faithfulness assumption is needed here. -/
theorem normalizer_semilinear (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (h : H) : ∃ σ : F ≃+* F, ∀ (c : F) (v : Fin 3 → F),
      ρ h (c • v) = σ c • ρ h v := by
  let f (c : F) : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => ρ h (c • ρ h⁻¹ v)
      map_zero' := by simp
      map_add' := by intro v w; simp [smul_add] }
  have hf (c : F) : ∃ d : F, ∀ v, f c v = d • v := by
    apply centralizer_scalar
    intro g v
    let x : L := e.symm g
    let y : L := ⟨h⁻¹ * (x : H) * h, (inferInstance : L.Normal).conj_mem' x x.property h⟩
    have hx (v : Fin 3 → F) : g.val.mulVec v = ρ (x : H) v := by
      rw [hnat]
      simp [x]
    have hy (c : F) (v : Fin 3 → F) : ρ (y : H) (c • v) = c • ρ (y : H) v := by
      simp only [hnat, Matrix.mulVec_smul]
    have hy₁ (v : Fin 3 → F) : ρ h⁻¹ (ρ (x : H) v) = ρ (y : H) (ρ h⁻¹ v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel, mul_one]
    have hy₂ (v : Fin 3 → F) : ρ h (ρ (y : H) v) = ρ (x : H) (ρ h v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel_left]
    change ρ h (c • ρ h⁻¹ (g.val.mulVec v)) = g.val.mulVec (ρ h (c • ρ h⁻¹ v))
    rw [hx, hx, hy₁, ← hy, hy₂]
  let φ : F → F := fun c => (f c (Pi.single 0 1)) 0
  have hφ (c : F) (v : Fin 3 → F) : f c v = φ c • v := by
    obtain ⟨d, hd⟩ := hf c
    have he : φ c = d := by simp [φ, hd]
    exact he ▸ hd v
  have hcancel (v : Fin 3 → F) : ρ h (ρ h⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hcancel' (v : Fin 3 → F) : ρ h⁻¹ (ρ h v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hmul (a b : F) (v : Fin 3 → F) : f (a * b) v = f a (f b v) := by
    simp [f, hcancel', mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, f, hcancel]
      map_mul' := by
        intro a b
        change (f (a * b) (Pi.single 0 1)) 0 = φ a * φ b
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
end Representation.SL3OddNaturalNormalizer

namespace Representation.SL3OddNaturalNormalizer
variable {F H : Type*} [Field F] [Algebra (ZMod 2) F] [Group H]

/-- An invertible semilinear actor determines its scalar automorphism uniquely. -/
theorem semilinear_coefficient_unique
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (h : H)
    {σ τ : F ≃+* F}
    (hσ : ∀ c v, ρ h (c • v) = σ c • ρ h v)
    (hτ : ∀ c v, ρ h (c • v) = τ c • ρ h v) : σ = τ := by
  have hcancel (v : Fin 3 → F) : ρ h (ρ h⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  ext c
  have he := (hσ c (ρ h⁻¹ (Pi.single 0 1))).symm.trans (hτ c (ρ h⁻¹ (Pi.single 0 1)))
  simpa only [hcancel, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
    using congrFun he 0

/-- The actual action on field scalars supplied by semilinearity. -/
@[expose] noncomputable def fieldAction
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v) :
    H →* (F ≃+* F) where
  toFun h := (hsemi h).choose
  map_one' := semilinear_coefficient_unique ρ 1 (hsemi 1).choose_spec (by simp)
  map_mul' a b := semilinear_coefficient_unique ρ (a * b) (hsemi (a * b)).choose_spec
    (by
      intro c v
      rw [map_mul]
      change ρ a (ρ b (c • v)) = (hsemi a).choose ((hsemi b).choose c) • ρ a (ρ b v)
      rw [(hsemi b).choose_spec, (hsemi a).choose_spec])

/-- The coefficient action satisfies the supplied semilinearity equation. -/
theorem fieldAction_smul
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v)
    (h : H) (c : F) (v : Fin 3 → F) :
    ρ h (c • v) = fieldAction ρ hsemi h c • ρ h v := (hsemi h).choose_spec c v

/-- Trivial coefficient action is exactly linearity over the field. -/
theorem fieldAction_eq_one_iff
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v)
    (h : H) : fieldAction ρ hsemi h = 1 ↔ ∀ (c : F) (v : Fin 3 → F), ρ h (c • v) = c • ρ h v := by
  constructor
  · intro he c v
    simpa only [he, RingAut.one_apply] using fieldAction_smul ρ hsemi h c v
  · exact fun hl => semilinear_coefficient_unique ρ h (fieldAction_smul ρ hsemi h) hl


end Representation.SL3OddNaturalNormalizer
