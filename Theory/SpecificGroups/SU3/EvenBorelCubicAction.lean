module
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Theory.SpecificGroups.SU3.BorelTorus.BorelResiduals
public import Theory.SpecificGroups.SU3.BorelTorus.BorelResiduals.Quotients
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.FieldTheory.CubicDisplacement
public import Theory.NumberTheory.BinaryTorusParity
public import BenderSuzuki.External.Huppert.II.theorem_10_13
/-!
# Cubic rigidity on the full even-degree unitary Borel

In even binary degree, the projective torus parametrization has trivial
kernel: its norm-one cubic kernel has order gcd(2^n+1,3)=1. A root-preserving
automorphism has a triangular semilinear representative. On the full Borel
quotient its action is the coefficient-field automorphism. Cubic displacement
therefore fixes all field cubes, forcing that automorphism to be identity
because the coefficient field has at least sixteen elements.

The two-core identification is explicit. The actual marked Sylow application
in Chapter12.Section06.NaturalSource.UnitaryBorelField supplies it from the
proved unitary Borel geometry, before pulling back through the original map.
Source: Aschbacher--Smith 12.6.31, printed pp.836--837; Huppert II.10.12--13.
-/
public section
open Subgroup Matrix BenderSuzuki.External Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The full projective torus has faithful unit coordinates in even degree. -/
theorem even_projective_torus_injective
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (he : Even n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n)) :
    Function.Injective (hermitianTorusPSU J hJ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply card_eq_one.mp
  rw [projective_ker_card J hJ hcard hconj]
  apply Nat.Coprime.gcd_eq_one
  apply Nat.Coprime.symm
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  have hm := Nat.BinaryTorusParity.two_pow_mod_three n
  rw [Nat.even_iff.mp he,if_pos rfl] at hm
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

/-- Cubic displacement on the full Borel quotient vanishes in even degree. -/
theorem standard_borel_displacement_mem_of_cube
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (he : Even n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hcore : (projectiveBorel J hJ).pCoreIn 2 = projectiveRoot J hJ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hc : ∀ x ∈ projectiveBorel J hJ, (a x * x⁻¹)^3 ∈ projectiveRoot J hJ) :
    ∀ x ∈ projectiveBorel J hJ, a x * x⁻¹ ∈ projectiveRoot J hJ := by
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
  have hd := SemilinearActors.projective_semilinear_torus_displacement J hJ
    a σ u h10 h20 h21 hu
  let B := projectiveBorel J hJ
  let R := projectiveRoot J hJ
  have hB : B.map a.toMonoidHom = B := by
    apply eq_of_le_of_card_ge
    · rw [show B = R ⊔ projectiveTorus J hJ from rfl,Subgroup.map_sup,hroot]
      apply sup_le le_sup_left
      rintro _ ⟨x,⟨k,rfl⟩,rfl⟩
      have hm := B.mul_mem ((show R ≤ B from le_sup_left) (hd k))
        ((show projectiveTorus J hJ ≤ B from le_sup_right) (show hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k) ∈
          projectiveTorus J hJ from ⟨_,rfl⟩))
      change a (hermitianTorusPSU J hJ k) ∈ B
      simpa only [inv_mul_cancel_right] using hm
    · rw [card_map_of_injective a.injective]
  let b : MulAut B := (a.subgroupMap B).trans (MulEquiv.subgroupCongr hB)
  let π := QuotientGroup.mk' (pCore 2 B)
  let t := projectiveTorusIn J hJ
  let f := π.comp t
  have hk (x : B) : π x = 1 ↔ (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ R := by
    refine (QuotientGroup.eq_one_iff x).trans ?_
    have hh := congrArg (subgroupOf · B) hcore
    rw [show (B.pCoreIn 2).subgroupOf B = pCore 2 B from
      comap_map_eq_self_of_injective B.subtype_injective _] at hh
    exact Iff.of_eq (congrArg (fun U : Subgroup B => x ∈ U) hh)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro k hkf
    have hr : hermitianTorusPSU J hJ k ∈ R := (hk (t k)).mp hkf
    have hone := Subgroup.disjoint_def.mp
      (SemilinearActors.projective_root_disjoint_torus J hJ) hr
      (show hermitianTorusPSU J hJ k ∈ projectiveTorus J hJ from ⟨_,rfl⟩)
    exact mem_bot.mpr ((even_projective_torus_injective J hJ he hcard hconj)
      (hone.trans (map_one _).symm))
  let et := quotientTorusEquiv B R (projectiveTorus J hJ) le_sup_right hcore
    (SemilinearActors.projective_root_disjoint_torus J hJ) rfl
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨k,hk'⟩ := (et y).property
    refine ⟨k,et.injective ?_⟩
    exact (quotientTorusEquiv_torus B R (projectiveTorus J hJ) le_sup_right hcore
      (SemilinearActors.projective_root_disjoint_torus J hJ) rfl
      ⟨hermitianTorusPSU J hJ k,⟨k,rfl⟩⟩).trans (Subtype.ext hk')
  have hact (k : Eˣ) : π (b (t k)) = f (Units.map σ.toMonoidHom k) := by
    change π (b (t k)) = π (t (Units.map σ.toMonoidHom k))
    apply mul_inv_eq_one.mp
    rw [←map_inv,←map_mul]
    exact (hk _).mpr (hd k)
  have hσ : σ = 1 := by
    apply (FiniteField.eq_one_or_card_le_four_of_unit_displacement_cube σ ?_).resolve_right
    · intro hsmall
      rw [hcard] at hsmall
      have h4 : 4 ≤ 2^n := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hn
      nlinarith
    · intro k
      apply hfi
      rw [map_pow,map_mul,map_inv,map_one,←hact]
      change (π (b (t k)) * (π (t k))⁻¹)^3 = 1
      rw [←map_inv,←map_mul,←map_pow]
      exact (hk _).mpr (hc (t k) (t k).property)
  have hfix (x : B) : π (b x) = π x := by
    obtain ⟨k,hk'⟩ := hfs (π x)
    have hh := congrArg (quotientAut (pCore 2 B) b) hk'
    change quotientAut (pCore 2 B) b (π (t k)) = quotientAut (pCore 2 B) b (π x) at hh
    rw [quotientAut_apply_mk,quotientAut_apply_mk,hact,hσ] at hh
    exact hh.symm.trans hk'
  intro x hx
  let xx : B := ⟨x,hx⟩
  exact (hk (b xx * xx⁻¹)).mp (by rw [map_mul,map_inv,hfix,mul_inv_cancel])
end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
