module

public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
public import Theory.FieldTheory.ScalarTwistedFixedPoints

/-!
# Strict fixed-point loss on the binary PSL₂ root group

An automorphism preserving the upper root group has scalar-semilinear root
coordinates once an inner-field factorization is supplied. Its inner factor
normalizes the root group, hence comes from the actual upper triangular Borel.
For an outer involution the field factor is a nontrivial involution. The
scalar-twisted fixed-field estimate gives strict loss above field order four.

The root module is the additive group of the field. Source: the linear
outer-offender calculation in Aschbacher–Smith 16.5.1, printed p.1194, using
GLS4, Chapter 4, Lemma 3.1(a). Semilinear coverage is an explicit input here.
-/

public section

open Subgroup BenderSuzuki.Converse
open scoped MatrixGroups
namespace Theory.PSL2.RootSemilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
variable {F : Type*} [Field F] [CharP F 2]

theorem fieldAut_root (σ : F ≃+* F) (t : Multiplicative F) :
    fieldAut σ (unipotentHom F t) =
      unipotentHom F (Multiplicative.ofAdd (σ t.toAdd)) := by
  change fieldAut σ (quotientMap F (uni t.toAdd)) = _
  rw [fieldAut_apply_quotientMap]
  apply congrArg (quotientMap F)
  ext i j
  change σ ((uni t.toAdd).val i j) = (uni (σ t.toAdd)).val i j
  fin_cases i <;> fin_cases j <;> simp

theorem fieldAut_map_kernel (σ : F ≃+* F) :
    (kernel F).map (fieldAut σ).toMonoidHom = kernel F := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    change fieldAut σ (unipotentHom F t) ∈ kernel F
    rw [fieldAut_root]
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨unipotentHom F (Multiplicative.ofAdd (σ.symm t.toAdd)), ⟨_, rfl⟩, ?_⟩
    change fieldAut σ (unipotentHom F (Multiplicative.ofAdd (σ.symm t.toAdd))) = _
    rw [fieldAut_root]
    change unipotentHom F (Multiplicative.ofAdd (σ (σ.symm t.toAdd))) = _
    rw [σ.apply_symm_apply]
    rfl

theorem scalar_action (a : MulAut (Group F))
    (hnorm : (kernel F).map a.toMonoidHom = kernel F)
    (g : Group F) (σ : F ≃+* F) (ha : a = MulAut.conj g * fieldAut σ) :
    ∃ c : F, ∀ t : Multiplicative F,
      a (unipotentHom F t) = unipotentHom F (Multiplicative.ofAdd (c * σ t.toAdd)) := by
  have hg : g ∈ normalizer (kernel F : Set (Group F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (kernel F).map (MulAut.conj g).toMonoidHom =
          ((kernel F).map (fieldAut σ).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        rw [fieldAut_map_kernel]
      _ = (kernel F).map a.toMonoidHom := by
        rw [map_map]
        congr 1
        ext x
        rw [ha]
        rfl
      _ = kernel F := hnorm
  rw [normalizer_kernel, borel_eq_PBorel, PBorel_eq_map] at hg
  obtain ⟨B, hB, rfl⟩ := hg
  refine ⟨(B.val 0 0)^2, fun t => ?_⟩
  rw [ha, MulAut.mul_apply, fieldAut_root]
  change pi F B * pi F (uni (σ t.toAdd)) * (pi F B)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, Borel_conj_uni hB]
  rfl

theorem fixed_card_lt [Finite F] (hF : 4 < Nat.card F)
    (a : MulAut (Group F)) (hnorm : (kernel F).map a.toMonoidHom = kernel F)
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g : Group F, a = MulAut.conj g)
    (hcoverage : ∃ (g : Group F) (σ : F ≃+* F), a = MulAut.conj g * fieldAut σ) :
    2 * Nat.card {u : kernel F // a u = u} < Nat.card (kernel F) := by
  obtain ⟨g, σ, he⟩ := hcoverage
  have hs := (semilinear_involution_data σ g (he ▸ ha)).1
  have hne : σ ≠ RingEquiv.refl F := by
    intro h
    apply houter
    exact ⟨g, by simpa only [h, fieldAut_refl, mul_one] using he⟩
  obtain ⟨c, hc⟩ := scalar_action a hnorm g σ he
  let e : Multiplicative F ≃* kernel F := MonoidHom.ofInjective (unipotentHom_injective F)
  have heval (u : kernel F) : unipotentHom F (e.symm u) = u :=
    congrArg Subtype.val (e.apply_symm_apply u)
  let f : {u : kernel F // a u = u} → {x : F // c * σ x = x} := fun u =>
    ⟨(e.symm u.val).toAdd, by
      apply Multiplicative.ofAdd.injective
      apply unipotentHom_injective F
      rw [← hc, heval]
      change a (u.val : Group F) = unipotentHom F (e.symm u.val)
      rw [heval]
      exact u.property⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    apply e.symm.injective
    exact Multiplicative.toAdd.injective (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [card_kernel]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcard)
    (FiniteField.two_mul_card_scalar_fixed_lt hF σ hs hne c)
end Theory.PSL2.RootSemilinear
