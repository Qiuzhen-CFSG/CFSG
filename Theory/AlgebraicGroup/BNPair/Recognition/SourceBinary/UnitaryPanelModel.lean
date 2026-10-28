module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BorelInnerPanel
public import Theory.SpecificGroups.SU3.SpecialBorelCubicAction
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors

/-!
# Unitary Borel two-group actors are root inner

For SU3 and its actual projective image over a binary field of fixed-field
order q at least four, an automorphism preserving the root has a triangular
semilinear representative. Trivial action on the full Borel quotient fixes
the torus parameters. In PSU3 this retains the cubic scalar kernel; finite
field rigidity still kills the field automorphism. In SU3 the torus map is
injective. Removing the root inner actor leaves an odd diagonal actor in
the original two-group, hence the identity.

This proves the concrete automorphism premise of BorelInnerPanel for both
carriers. No projective simplicity or semilinear-coverage hypothesis is
left to the caller. The parameter q = 2 is deliberately outside this
calculation and remains a separate source branch.
Source: Fong--Seitz I (2B), pp.7--9, using Huppert II.10.12--13 and the
unitary semilinear formulas (GLS3 Section 2.7).
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.External BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

 theorem projective_borel_two_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n)) :
    BorelTwoInner (projectiveRoot J hJ) (projectiveBorel J hJ) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  intro A hA hRA a ha hroot hdisp
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
      have h4 : 4 ≤ 2^n := Nat.pow_le_pow_right (show 1 ≤ (2:ℕ) by decide) hn
      nlinarith
    · intro k
      apply ((projective_eq_one_iff J hJ _).mp ?_).2
      rw [map_mul,map_inv]
      have hk := (SemilinearActors.projective_semilinear_torus_displacement_iff
        J hJ a σ u h10 h20 h21 hu k).mp
          (hdisp _ (show hermitianTorusPSU J hJ k ∈ projectiveBorel J hJ from
            mem_sup_right ⟨k,rfl⟩))
      rw [hk,mul_inv_cancel]
  apply SemilinearActors.projective_identity_field_mem_root_inner J hJ hcard
    (by omega) A hA hRA a ha u h10 h20 h21
  intro x
  have hsid : σ.toRingHom = RingHom.id E := by rw [hσ]; rfl
  simpa only [hsid, ProjGenLinGroup.map_id, MonoidHom.id_apply] using hu x

 theorem special_borel_two_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n)) :
    BorelTwoInner (specialRoot J hJ) (specialBorel J hJ) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  intro A hA hRA a ha hroot hdisp
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨σ,u,hu⟩ := EvenSemilinear.special_semilinear_coverage J hJ hn hcard hconj a
  obtain ⟨h10,h20,h21⟩ := SemilinearActors.special_semilinear_upper J hJ
    hcard hfixed a σ u hu hroot
  have hσ : σ = 1 := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · let k : Eˣ := Units.mk0 x hx
      have hk := (SemilinearActors.special_semilinear_torus_displacement_iff
        J hJ a σ u h10 h20 h21 hu k).mp
          (hdisp _ (show hermitianTorusSU J hJ k ∈ specialBorel J hJ from
            mem_sup_right ⟨k,rfl⟩))
      exact congrArg Units.val ((special_injective J hJ) hk)
  apply SemilinearActors.special_identity_field_mem_root_inner J hJ hcard
    (by omega) A hA hRA a ha u h10 h20 h21
  intro x
  have hsid : σ.toRingHom = RingHom.id E := by rw [hσ]; rfl
  simpa only [hsid, GeneralLinearGroup.map_id, MonoidHom.id_apply] using hu x
end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
