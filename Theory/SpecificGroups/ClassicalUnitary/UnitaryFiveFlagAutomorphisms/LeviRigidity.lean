module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.TorusRigidity
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.TensorVanishing

/-!
# Vanishing of the central plane-Levi displacement

The remaining central displacement is a cocycle for the actual twisted tensor
matrix action. The established first-cohomology theorem makes it principal.
Fixation of the order-fifteen torus forces the principal matrix to zero,
because none of its four matrix weights is one. Thus the entire SL₂ Levi
is fixed, without a conjugacy assertion for arbitrary Levi complements.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf;
the cohomology calculation is I.1.6(3), printed p.408.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
open PlaneCore PlaneCore.ResidualAction Representation.OrthogonalFourMinus
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem matrix_torus_fixed_zero (hconj : ∀ b, J.conj b = b ^ 4)
    (t : Fˣ) (ht : orderOf t = 15) (X : Mat F)
    (hX : tensorAction J.conj (diagonalActor t) X = X) : X = 0 := by
  have hp (n : ℕ) (hn : ¬15 ∣ n) : t^n ≠ 1 := by
    intro hh
    exact hn (ht ▸ orderOf_dvd_of_pow_eq_one hh)
  have hw (i j : Fin 2) : (![t,t⁻¹] : Fin 2 → Fˣ) i *
      (![t,t⁻¹] : Fin 2 → Fˣ) j ^ 4 ≠ 1 := by
    fin_cases i <;> fin_cases j <;> dsimp
    · convert hp 5 (by decide) using 1
      group
    · rw [show t*t⁻¹^4=(t^3)⁻¹ by group]
      simpa only [ne_eq,inv_eq_one] using hp 3 (by decide)
    · convert hp 3 (by decide) using 1
      group
    · rw [show t⁻¹*t⁻¹^4=(t^5)⁻¹ by group]
      simpa only [ne_eq,inv_eq_one] using hp 5 (by decide)
  have he (i j : Fin 2) :
      (((![t,t⁻¹] : Fin 2 → Fˣ) i * (![t,t⁻¹] : Fin 2 → Fˣ) j ^ 4 : Fˣ) : F) * X i j = X i j := by
    have hh := congrArg (fun Y : Mat F => Y i j) hX
    change ((diagonalActor t).val * X * adjoint J.conj (diagonalActor t).val) i j = X i j at hh
    fin_cases i <;> fin_cases j <;>
      simpa [diagonalActor,adjoint,Matrix.mul_apply,Fin.sum_univ_two,hconj, mul_assoc,mul_comm,mul_left_comm] using hh
  ext i j
  by_contra hh
  exact hw i j (Units.ext ((mul_eq_right₀ hh).mp (he i j)))

variable [Finite F]

/-- A central Levi displacement fixing the order-fifteen torus is zero. -/
theorem leviDeviation_eq_one_of_center (hconj : ∀ b, J.conj b = b ^ 4)
    (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (PlaneSemidirect J)) (ha : ∀ p, (a p).right = p.right)
    (hcentral : ∀ A, (leviDeviation J a A).x = 0)
    (t : Fˣ) (ht : orderOf t = 15)
    (hfix : a (SemidirectProduct.inr (diagonalActor t)) = SemidirectProduct.inr (diagonalActor t)) :
    ∀ A, leviDeviation J a A = 1 := by
  let f : Representation.OneCohomology.cocycles (tensorAction J.conj) :=
    ⟨fun A => (leviDeviation J a A).z, by
      intro A B
      change (leviDeviation J a (A*B)).z = _
      rw [leviDeviation_mul J a ha,add_comm]
      ext i j
      simp only [Parameters.mul_z,hcentral,Pi.zero_apply,zero_mul,add_zero,
        Parameters.planeAction_z]
      rfl⟩
  have hσ : ∃ x : F, J.conj x ≠ x := by
    refine ⟨c,?_⟩
    intro hh
    rw [hh,CharTwo.add_self_eq_zero] at hc
    exact zero_ne_one hc
  obtain ⟨X,hX⟩ := tensorAction_principal_surjective J.conj hσ f
  have hT : tensorAction J.conj (diagonalActor t) X = X := by
    have hh := congrArg (fun g : Representation.OneCohomology.cocycles (tensorAction J.conj) =>
      g.val (diagonalActor t)) hX
    have hd : leviDeviation J a (diagonalActor t) = 1 := congrArg SemidirectProduct.left hfix
    change tensorAction J.conj (diagonalActor t) X - X = (leviDeviation J a (diagonalActor t)).z at hh
    rw [hd,Parameters.one_z] at hh
    exact sub_eq_zero.mp hh
  have hzero : X = 0 := matrix_torus_fixed_zero J hconj t ht X hT
  intro A
  apply Parameters.ext (hcentral A)
  have hh := congrArg (fun g : Representation.OneCohomology.cocycles (tensorAction J.conj) => g.val A) hX
  rw [hzero,map_zero] at hh
  exact hh.symm
end Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
