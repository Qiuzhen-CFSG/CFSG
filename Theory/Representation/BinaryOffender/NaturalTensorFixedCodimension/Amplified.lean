module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.SpecialLinearNatural
import Mathlib.Tactic

/-!
# Intertwiners on sums of natural SL₂ modules

Write the natural isotypic module as M × M, with SL₂ acting on the two
coordinates. Intertwining the upper and lower root groups forces a pure field
intertwiner to apply the same semilinear map to both multiplicity coordinates.
Removing an inner matrix gives the corresponding inner-field statement.
For a nontrivial inner involution, one off-diagonal entry is nonzero, so projection
onto one coordinate is injective on fixed vectors. Rank-nullity gives the bound.

No assumption that the operator preserves individual natural summands is used.
Source: GLS, vol. 2, Theorem 26.24, final paragraph, ChapterG.tex, lines 1240–1248.
-/

@[expose] public section

open Module
namespace Representation.BinaryOffender.NaturalTensor
variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- The natural SL₂ action with multiplicity space M. -/
def amplifiedNatural : Representation F (Matrix.SpecialLinearGroup (Fin 2) F) (M × M) where
  toFun g := ((g.val 0 0 • LinearMap.fst F M M + g.val 0 1 • LinearMap.snd F M M).prod
    (g.val 1 0 • LinearMap.fst F M M + g.val 1 1 • LinearMap.snd F M M))
  map_one' := by ext v <;> simp
  map_mul' g h := by
    ext v <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_smul, mul_smul]

lemma amplifiedNatural_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : M × M) :
    amplifiedNatural g v =
      (g.val 0 0 • v.1 + g.val 0 1 • v.2, g.val 1 0 • v.1 + g.val 1 1 • v.2) := rfl

lemma amplifiedNatural_upper (a : F) (v : M × M) :
    amplifiedNatural (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) zero_ne_one a) v = (v.1 + a • v.2, v.2) := by
  simp [amplifiedNatural_apply, Matrix.SpecialLinearGroup.transvection_coe]

lemma amplifiedNatural_lower (a : F) (v : M × M) :
    amplifiedNatural (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) one_ne_zero a) v = (v.1, v.2 + a • v.1) := by
  simp [amplifiedNatural_apply, Matrix.SpecialLinearGroup.transvection_coe, add_comm]

variable {k : Type*} [Field k] [Algebra k F] [Module k M] [IsScalarTower k F M]

private lemma map_entry (σ : F →+* F) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (i j : Fin 2) : (Matrix.SpecialLinearGroup.map σ g).val i j = σ (g.val i j) := rfl

omit [Algebra k F] [IsScalarTower k F M] in
/-- All field intertwiners, with arbitrary multiplicity mixing. -/
theorem amplified_intertwiner (T : Module.End k (M × M)) (σ : F →+* F)
    (hT : ∀ g v, T (amplifiedNatural g v) =
      amplifiedNatural (Matrix.SpecialLinearGroup.map σ g) (T v)) :
    ∃ S : Module.End k M, (∀ a x, S (a • x) = σ a • S x) ∧
      ∀ v, T v = (S v.1, S v.2) := by
  have hu (a : F) (v : M × M) : T (v.1 + a • v.2, v.2) =
      ((T v).1 + σ a • (T v).2, (T v).2) := by
    simpa [amplifiedNatural_apply, Matrix.SpecialLinearGroup.transvection_coe,
      map_entry] using
      hT (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one a) v
  have hl (a : F) (v : M × M) : T (v.1, v.2 + a • v.1) =
      ((T v).1, (T v).2 + σ a • (T v).1) := by
    simpa [amplifiedNatural_apply, Matrix.SpecialLinearGroup.transvection_coe,
      map_entry, add_comm] using
      hT (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a) v
  have hu' (a : F) (y : M) : T (a • y, 0) = (σ a • (T (0, y)).2, 0) := by
    have h := congrArg (fun w => w - T (0, y)) (hu a (0, y))
    rw [← map_sub] at h
    apply Prod.ext
    · simpa using congrArg Prod.fst h
    · simpa using congrArg Prod.snd h
  have hl' (a : F) (x : M) : T (0, a • x) = (0, σ a • (T (x, 0)).1) := by
    have h := congrArg (fun w => w - T (x, 0)) (hl a (x, 0))
    rw [← map_sub] at h
    apply Prod.ext
    · simpa using congrArg Prod.fst h
    · simpa using congrArg Prod.snd h
  let S : Module.End k M := (LinearMap.fst k M M).comp (T.comp (LinearMap.inl k M M))
  have hleft (x : M) : T (x, 0) = (S x, 0) := by
    apply Prod.ext
    · rfl
    · simpa using congrArg Prod.snd (hu' 1 x)
  have hright (x : M) : T (0, x) = (0, S x) := by
    simpa [S] using hl' 1 x
  refine ⟨S, ?_, ?_⟩
  · intro a x
    have h := congrArg Prod.fst (hu' a x)
    simpa only [hleft, hright] using h
  · rintro ⟨x, y⟩
    have h : (x, y) = (x, 0) + (0, y) := by simp
    rw [h, map_add, hleft, hright]
    simp



/-- Removing the inner part leaves a scalar-semilinear multiplicity operator. -/
theorem amplified_inner_field_intertwiner
    (T : Module.End k (M × M)) (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hT : ∀ g v, T (amplifiedNatural g v) =
      amplifiedNatural (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    ∃ S : Module.End k M, (∀ a x, S (a • x) = σ a • S x) ∧
      ∀ v, T v = amplifiedNatural r (S v.1, S v.2) := by
  let R : Module.End k (M × M) := (amplifiedNatural r⁻¹).restrictScalars k
  let T' := R.comp T
  have hT' : ∀ g v, T' (amplifiedNatural g v) =
      amplifiedNatural (Matrix.SpecialLinearGroup.map σ g) (T' v) := by
    intro g v
    change amplifiedNatural r⁻¹ (T (amplifiedNatural g v)) =
      amplifiedNatural (Matrix.SpecialLinearGroup.map σ g) (amplifiedNatural r⁻¹ (T v))
    rw [hT]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  obtain ⟨S, hS, he⟩ := amplified_intertwiner T' σ hT'
  refine ⟨S, hS, fun v => ?_⟩
  rw [← he]
  change T v = amplifiedNatural r (amplifiedNatural r⁻¹ (T v))
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

/-- Inner-field intertwiners are semilinear even when natural summands mix. -/
theorem amplified_inner_field_semilinear
    (T : Module.End k (M × M)) (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hT : ∀ g v, T (amplifiedNatural g v) =
      amplifiedNatural (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    ∀ a v, T (a • v) = σ a • T v := by
  obtain ⟨S, hS, he⟩ := amplified_inner_field_intertwiner T r σ hT
  intro a v
  simp only [he, Prod.smul_fst, Prod.smul_snd, hS]
  exact (amplifiedNatural r).map_smul (σ a) (S v.1, S v.2)

/-- A nonidentity binary SL₂ involution has a nonzero off-diagonal entry. -/
lemma involution_off_diagonal [CharP F 2] (r : Matrix.SpecialLinearGroup (Fin 2) F)
    (hr : r * r = 1) (hne : r ≠ 1) : r.val 0 1 ≠ 0 ∨ r.val 1 0 ≠ 0 := by
  by_contra h
  push Not at h
  have he (i : Fin 2) := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.val i i) hr
  have h00 : r.val 0 0 = 1 := by
    have hsq : (r.val 0 0) ^ 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, pow_two] using he 0
    rcases sq_eq_one_iff.mp hsq with heq | heq
    · exact heq
    · simpa only [CharTwo.neg_eq] using heq
  have h11 : r.val 1 1 = 1 := by
    have hsq : (r.val 1 1) ^ 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, pow_two] using he 1
    rcases sq_eq_one_iff.mp hsq with heq | heq
    · exact heq
    · simpa only [CharTwo.neg_eq] using heq
  apply hne
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h.1, h.2]

/-- A nontrivial inner involution moves at least one full multiplicity space. -/
theorem amplified_inner_bound [CharP F 2] [FiniteDimensional k M]
    (T : Module.End k (M × M)) (hTi : Function.Injective T)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (amplifiedNatural g v) =
      amplifiedNatural (r * g * r⁻¹) (T v)) :
    finrank k M ≤ operatorFixedCodim T := by
  have hm (g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix.SpecialLinearGroup.map (RingHom.id F) g = g := by rfl
  obtain ⟨S, _, he⟩ := amplified_inner_field_intertwiner T r (RingHom.id F) (by
    simpa only [hm] using hT)
  have hS (x : M) (hx : S x = 0) : x = 0 := by
    have ht : T (x, 0) = 0 := by simp [he, hx, amplifiedNatural_apply]
    exact congrArg Prod.fst (hTi (ht.trans (map_zero T).symm))
  have hker : finrank k (LinearMap.ker (T - 1)) ≤ finrank k M := by
    rcases involution_off_diagonal r hr hne with hb | hc
    · let f := (LinearMap.fst k M M).domRestrict (LinearMap.ker (T - 1))
      apply LinearMap.finrank_le_finrank_of_injective (f := f)
      apply LinearMap.ker_eq_bot.mp
      apply (Submodule.eq_bot_iff _).mpr
      intro v hv
      have hx : v.val.1 = 0 := hv
      have hfix : T v.val = v.val := sub_eq_zero.mp v.property
      have hz : S v.val.2 = 0 := by
        have hh := congrArg Prod.fst hfix
        simpa [he, amplifiedNatural_apply, hx, (smul_eq_zero_iff_right hb)] using hh
      apply Subtype.ext
      exact Prod.ext hx (hS _ hz)
    · let f := (LinearMap.snd k M M).domRestrict (LinearMap.ker (T - 1))
      apply LinearMap.finrank_le_finrank_of_injective (f := f)
      apply LinearMap.ker_eq_bot.mp
      apply (Submodule.eq_bot_iff _).mpr
      intro v hv
      have hy : v.val.2 = 0 := hv
      have hfix : T v.val = v.val := sub_eq_zero.mp v.property
      have hz : S v.val.1 = 0 := by
        have hh := congrArg Prod.snd hfix
        simpa [he, amplifiedNatural_apply, hy, (smul_eq_zero_iff_right hc)] using hh
      apply Subtype.ext
      exact Prod.ext (hS _ hz) hy
  have hd := operatorFixedCodim_add_finrank T
  rw [Module.finrank_prod] at hd
  omega

end Representation.BinaryOffender.NaturalTensor
