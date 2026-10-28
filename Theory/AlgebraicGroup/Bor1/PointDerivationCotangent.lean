module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Theory.AlgebraicGroup.Bor1.Differential

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Derivations at the identity are the linear dual of the cotangent space
`m / m^2` of the identity-point ideal. -/
@[expose] public noncomputable def identityPointDerivationEquivCotangentDual
    (K : Variety k) [AlgebraicGroup K] :
    IdentityPointDerivation K ≃ₗ[k]
      ((K.pointPrime 1).asIdeal.Cotangent →ₗ[k] k) := by
  let A := Variety.PolynomialFunction K
  let ev : A →ₐ[k] k := polynomialFunctionPointAlgHom K 1
  let m : Ideal A := (K.pointPrime 1).asIdeal
  let center : A →ₗ[k] m := {
    toFun a := ⟨a - algebraMap k A (ev a), by
      change ev a - ev (algebraMap k A (ev a)) = 0
      rw [ev.commutes]
      exact sub_self _⟩
    map_add' a b := by
      apply Subtype.ext
      change a + b - algebraMap k A (ev (a + b)) =
        (a - algebraMap k A (ev a)) + (b - algebraMap k A (ev b))
      rw [map_add, map_add]
      abel
    map_smul' c a := by
      apply Subtype.ext
      change c • a - algebraMap k A (ev (c • a)) =
        c • (a - algebraMap k A (ev a))
      rw [map_smul ev]
      simp only [Algebra.smul_def]
      rw [map_mul]
      simp [mul_sub] }
  let forward : IdentityPointDerivation K →ₗ[k] (m.Cotangent →ₗ[k] k) := {
    toFun D := Ideal.Cotangent.lift
      ((D : A →ₗ[k] k).comp (m.subtype.restrictScalars k)) (by
        intro x y
        change D ((x : A) * (y : A)) = 0
        rw [D.leibniz]
        change ev x * D y + ev y * D x = 0
        rw [show ev x = 0 from x.2, show ev y = 0 from y.2]
        simp)
    map_add' D E := by
      ext x
      obtain ⟨x, rfl⟩ := m.toCotangent_surjective x
      rfl
    map_smul' c D := by
      ext x
      obtain ⟨x, rfl⟩ := m.toCotangent_surjective x
      rfl }
  have center_mul_cotangent (a b : A) :
      m.toCotangent (center (a * b)) =
        ev a • m.toCotangent (center b) +
          ev b • m.toCotangent (center a) := by
    calc
      m.toCotangent (center (a * b)) =
          m.toCotangent (ev a • center b + ev b • center a) := by
        rw [m.toCotangent_eq]
        change (a * b - algebraMap k A (ev (a * b))) -
            (algebraMap k A (ev a) * (b - algebraMap k A (ev b)) +
              algebraMap k A (ev b) * (a - algebraMap k A (ev a))) ∈ m ^ 2
        have heq :
            (a * b - algebraMap k A (ev (a * b))) -
                (algebraMap k A (ev a) * (b - algebraMap k A (ev b)) +
                  algebraMap k A (ev b) * (a - algebraMap k A (ev a))) =
              (a - algebraMap k A (ev a)) *
                (b - algebraMap k A (ev b)) := by
          rw [map_mul ev, map_mul (algebraMap k A)]
          ring
        rw [heq, pow_two]
        exact Ideal.mul_mem_mul (center a).2 (center b).2
      _ = ev a • m.toCotangent (center b) +
          ev b • m.toCotangent (center a) := by
        change (m.toCotangent.restrictScalars k)
            (ev a • center b + ev b • center a) = _
        rw [map_add, map_smul, map_smul]
        rfl
  let backward : (m.Cotangent →ₗ[k] k) →ₗ[k] IdentityPointDerivation K := {
    toFun l := Derivation.mk'
      (l.comp ((m.toCotangent.restrictScalars k).comp center)) (by
        intro a b
        change l (m.toCotangent (center (a * b))) =
          ev a * l (m.toCotangent (center b)) +
            ev b * l (m.toCotangent (center a))
        rw [center_mul_cotangent, map_add, map_smul, map_smul]
        simp only [smul_eq_mul])
    map_add' l q := by
      ext a
      rfl
    map_smul' c l := by
      ext a
      rfl }
  have left_inv : Function.LeftInverse backward forward := by
    intro D
    apply Derivation.ext
    intro a
    change D (a - algebraMap k A (ev a)) = D a
    rw [map_sub, D.map_algebraMap, sub_zero]
  have right_inv : Function.RightInverse backward forward := by
    intro l
    ext z
    obtain ⟨x, rfl⟩ := m.toCotangent_surjective z
    change l (m.toCotangent (center (x : A))) = l (m.toCotangent x)
    have hx : ev (x : A) = 0 := x.2
    simp [center, hx]
  exact LinearEquiv.mk forward backward left_inv right_inv

end Theory.AlgebraicGroup.Bor1
