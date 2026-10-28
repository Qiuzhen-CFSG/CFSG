module
public import Theory.SpecificGroups.SU3.EvenBorelCubicAction
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors

/-!
# Inner Sylow actors fixing the full unitary Borel quotient

For binary PSU₃(q), q ≥ 4, an automorphism preserving the standard root
and fixing the full Borel modulo that root has trivial field part. Indeed
its field displacement lies in the cubic kernel of the torus parametrization;
cubic rigidity over the coefficient field forces identity. If the actor
belongs to a two-group containing the root inner image, the remaining odd
diagonal part vanishes, so the actor is conjugation by an actual root element.

The two-group is retained explicitly for the original Sylow application.
There is no exceptional q = 8 case for full fixation (as opposed to cubic
displacement). Source: Aschbacher–Smith 14.7.41, printed p.1061,
refs/quasithin.pdf; the matrix coordinates are Huppert II.10.12–13.
-/

public section
open Subgroup Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

theorem fixed_standard_borel_actor_mem_root_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : IsPGroup 2 A) (hRA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hc : ∀ x ∈ projectiveBorel J hJ, a x * x⁻¹ ∈ projectiveRoot J hJ) :
    a ∈ (projectiveRoot J hJ).map MulAut.conj := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2^n) hq hcard hfixed
  obtain ⟨σ,u,hu⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  obtain ⟨h10,h20,h21⟩ := SemilinearActors.projective_semilinear_upper J hJ
    hcard hfixed a σ u hu hroot
  have hσ : σ = 1 := by
    apply (FiniteField.eq_one_or_card_le_four_of_unit_displacement_cube σ ?_).resolve_right
    · intro hsmall
      rw [hcard] at hsmall
      have h4 : 4 ≤ 2^n := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hn
      nlinarith
    · intro k
      have he := (SemilinearActors.projective_semilinear_torus_displacement_iff
        J hJ a σ u h10 h20 h21 hu k).mp
        (hc _ ((show projectiveTorus J hJ ≤ projectiveBorel J hJ from le_sup_right) ⟨k,rfl⟩))
      have hk : hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k * k⁻¹) = 1 := by
        rw [map_mul,map_inv,he,mul_inv_cancel]
      exact ((projective_eq_one_iff J hJ _).mp hk).2
  apply SemilinearActors.projective_identity_field_mem_root_inner J hJ hcard
    (by omega) A hA hRA a ha u h10 h20 h21
  intro x
  have hsid : σ.toRingHom = RingHom.id E := by rw [hσ]; rfl
  simpa only [hsid,ProjGenLinGroup.map_id,MonoidHom.id_apply] using hu x
end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
