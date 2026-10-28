module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal

/-!
# The scalar kernel in the unitary order-nine branch

When p ≡ 2 modulo three, every cube root of unity has unitary norm one
for x ↦ x^p. Scalar matrices thus identify the kernel of the actual
SU₃ → PSU₃ projection with the cube roots of unity in the matrix field.
The finite cyclic multiplicative group has exactly three such roots.

This proves the required kernel order for arbitrary Hermitian Gram matrices,
without a group-order formula, simplicity theorem or multiplier assertion.
Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); compare A.3.21(c), printed pp.55–56.
-/

@[expose] public section

open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The scalar kernel has order three when p ≡ 2 modulo three. -/
theorem scalar_kernel_card {p : ℕ} (hmod : p % 3 = 2)
    (hcard : Nat.card E = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    Nat.card J.specialToProjective.ker = 3 := by
  let C := (powMonoidHom 3 : Eˣ →* Eˣ).ker
  have hnorm (x : C) : J.conj (x.val : E) * x.val = 1 := by
    have hx : (x.val : E) ^ 3 = 1 := congrArg Units.val x.property
    rw [hconj, pow_eq_pow_of_modEq (show p ≡ 2 [MOD 3] from hmod) hx, ← pow_succ]
    exact hx
  let f : C → J.specialToProjective.ker := fun x =>
    ⟨⟨GeneralLinearGroup.scalar (Fin 3) x.val,
      J.scalar_mem_unitary_of_norm_one x.val (hnorm x), by
        change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) x.val) = 1
        simpa only [GeneralLinearGroup.det_scalar, Fintype.card_fin] using
          (show x.val ^ 3 = 1 from x.property)⟩, by
      apply Subtype.ext
      rw [J.specialToProjective_apply_val]
      change ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) x.val) = 1
      apply ProjGenLinGroup.mk_eq_one.mpr
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨x.val, rfl⟩⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Units.ext
    have hh := congrArg (fun z : J.specialToProjective.ker => z.val.val.val 0 0) h
    simpa [f, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hh
  have hs : Function.Surjective f := by
    intro x
    have hz : x.val.val ∈ center (GL (Fin 3) E) := by
      apply ProjGenLinGroup.mk_eq_one.mp
      simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
        congrArg Subtype.val x.property
    rw [GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨d, hd⟩ := hz
    have hd3 : d ^ 3 = 1 := by
      have hh : GeneralLinearGroup.det x.val.val = 1 := x.val.property.2
      rw [← hd, GeneralLinearGroup.det_scalar] at hh
      simpa using hh
    exact ⟨⟨d, hd3⟩, Subtype.ext (Subtype.ext hd)⟩
  have heq : Nat.card J.specialToProjective.ker = Nat.card C :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm
  rw [heq, IsCyclic.card_powMonoidHom_ker]
  apply Nat.gcd_eq_right
  rw [Nat.card_units, hcard, Nat.dvd_iff_mod_eq_zero]
  have hpl : 2 ≤ p := by omega
  have hp : 1 ≤ p ^ 2 := by nlinarith
  have hm : (p ^ 2) % 3 = 1 := by simp [Nat.pow_mod, hmod]
  omega

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
