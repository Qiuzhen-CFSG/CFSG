module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Scalar norm lifting for cubic coefficient automorphisms

For an order-three automorphism of a finite field, every nonzero fixed scalar
is a product `t * σ(t) * σ²(t)`. Apply finite-field norm surjectivity to the
fixed field of the actual cyclic automorphism subgroup. Artin's fixed-field
correspondence identifies its three automorphisms with the three powers of σ,
so the algebraic norm is exactly the product used by the matrix cocycle.

This removes the scalar obstruction in projective semilinear descent; it does
not assume that a matrix representative already has twisted cube one.
Source context: GLS3, Proposition 4.9.1(d), `refs/KGroup/GLS3/chapter4.tex`,
and Aschbacher–Smith, A.3.16–18, `refs/quasithin.pdf`, printed pp.51–53.
-/

public section

namespace Matrix.PSL3.StandardCubicFixedNine.Descent
variable {F : Type*} [Field F] [Finite F]

/-- Every nonzero fixed scalar is a cubic norm, for the specified generator σ. -/
theorem exists_cubic_norm (σ : F ≃+* F) (hs : orderOf σ = 3)
    (c : Fˣ) (hc : Units.map σ.toRingHom.toMonoidHom c = c) :
    ∃ t : Fˣ, t * Units.map σ.toRingHom.toMonoidHom t *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t) = c := by
  classical
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let G := Subgroup.zpowers σ
  let E := FixedPoints.subfield G F
  let : Fintype G := Fintype.ofFinite G
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  let e : Fin 3 ≃ G := (finCongr hs.symm).trans (finEquivZPowers hfin)
  have he (i : Fin 3) : (e i).val = σ ^ i.val := rfl
  have hfix : (c : F) ∈ E := by
    intro g
    obtain ⟨i, rfl⟩ := e.surjective g
    change (e i).val (c : F) = c
    rw [he]
    have hc' : σ (c : F) = c := congrArg Units.val hc
    fin_cases i <;> simp [pow_succ, hc']
  let cE : Eˣ := Units.mk0 ⟨c, hfix⟩ (by
    intro h
    exact c.ne_zero (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := FiniteField.unitsMap_norm_surjective E F cE
  refine ⟨t, ?_⟩
  apply Units.ext
  have ht' : algebraMap E F (Algebra.norm E (t : F)) = c :=
    congrArg (fun u : Eˣ => ((u.val : E) : F)) ht
  rw [Algebra.norm_eq_prod_automorphisms] at ht'
  have hp : (∏ f : F ≃ₐ[E] F, f (t : F)) =
      ∏ i : Fin 3, (σ ^ i.val) (t : F) := by
    exact (Fintype.prod_equiv (e.trans (FixedPoints.toAlgAutMulEquiv G F).toEquiv)
      (fun i : Fin 3 => (σ ^ i.val) (t : F))
      (fun f : F ≃ₐ[E] F => f (t : F)) (fun i => rfl)).symm
  rw [hp] at ht'
  simpa [Fin.prod_univ_succ, pow_succ, mul_assoc] using ht'

end Matrix.PSL3.StandardCubicFixedNine.Descent
