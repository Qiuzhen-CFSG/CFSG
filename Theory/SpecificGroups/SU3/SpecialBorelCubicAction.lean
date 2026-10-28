module
public import Theory.SpecificGroups.SU3.EvenBorelCubicAction
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors
/-!
# Cubic rigidity on the full special-unitary Borel

The special-unitary torus has faithful unit coordinates. Cubic displacement
on the full Borel quotient therefore fixes field cubes, so the field part
is trivial for binary degree at least two. Removing the triangular
representative's odd diagonal factor leaves a root inner automorphism
inside the original two-group of actors. The scalar center is retained.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup Matrix BenderSuzuki.External Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The full special Borel has trivial field action under cubic displacement. -/
theorem special_standard_borel_rigidity
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hcore : (specialBorel J hJ).pCoreIn 2 = specialRoot J hJ)
    (a : MulAut (J.specialSubgroup))
    (hroot : (specialRoot J hJ).map a.toMonoidHom = specialRoot J hJ)
    (hc : ∀ x ∈ specialBorel J hJ, (a x * x⁻¹)^3 ∈ specialRoot J hJ) :
    (∀ x ∈ specialBorel J hJ, a x * x⁻¹ ∈ specialRoot J hJ) ∧
    ∃ u : J.unitarySubgroup, u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧
      u.val.val 2 1 = 0 ∧
      ∀ x : J.specialSubgroup,
        (a x).val = u.val * x.val * u.val⁻¹ := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨σ,u,hu⟩ := EvenSemilinear.special_semilinear_coverage J hJ (by omega) hcard hconj a
  obtain ⟨h10,h20,h21⟩ := SemilinearActors.special_semilinear_upper J hJ
    hcard hfixed a σ u hu hroot
  have hd := SemilinearActors.special_semilinear_torus_displacement J hJ
    a σ u h10 h20 h21 hu
  let B := specialBorel J hJ
  let R := specialRoot J hJ
  have hB : B.map a.toMonoidHom = B := by
    apply eq_of_le_of_card_ge
    · rw [show B = R ⊔ specialTorus J hJ from rfl,Subgroup.map_sup,hroot]
      apply sup_le le_sup_left
      rintro _ ⟨x,⟨k,rfl⟩,rfl⟩
      have hm := B.mul_mem ((show R ≤ B from le_sup_left) (hd k))
        ((show specialTorus J hJ ≤ B from le_sup_right) (show hermitianTorusSU J hJ (Units.map σ.toMonoidHom k) ∈
          specialTorus J hJ from ⟨_,rfl⟩))
      change a (hermitianTorusSU J hJ k) ∈ B
      simpa only [inv_mul_cancel_right] using hm
    · rw [card_map_of_injective a.injective]
  let b : MulAut B := (a.subgroupMap B).trans (MulEquiv.subgroupCongr hB)
  let π := QuotientGroup.mk' (pCore 2 B)
  let t := specialTorusIn J hJ
  let f := π.comp t
  have hk (x : B) : π x = 1 ↔ (x : J.specialSubgroup) ∈ R := by
    refine (QuotientGroup.eq_one_iff x).trans ?_
    have hh := congrArg (subgroupOf · B) hcore
    rw [show (B.pCoreIn 2).subgroupOf B = pCore 2 B from
      comap_map_eq_self_of_injective B.subtype_injective _] at hh
    exact Iff.of_eq (congrArg (fun U : Subgroup B => x ∈ U) hh)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro k hkf
    have hr : hermitianTorusSU J hJ k ∈ R := (hk (t k)).mp hkf
    have hone := Subgroup.disjoint_def.mp
      (SemilinearActors.special_root_disjoint_torus J hJ) hr
      (show hermitianTorusSU J hJ k ∈ specialTorus J hJ from ⟨_,rfl⟩)
    exact mem_bot.mpr ((special_injective J hJ) (hone.trans (map_one _).symm))
  let et := quotientTorusEquiv B R (specialTorus J hJ) le_sup_right hcore
    (SemilinearActors.special_root_disjoint_torus J hJ) rfl
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨k,hk'⟩ := (et y).property
    refine ⟨k,et.injective ?_⟩
    exact (quotientTorusEquiv_torus B R (specialTorus J hJ) le_sup_right hcore
      (SemilinearActors.special_root_disjoint_torus J hJ) rfl
      ⟨hermitianTorusSU J hJ k,⟨k,rfl⟩⟩).trans (Subtype.ext hk')
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
  refine ⟨?_,u,h10,h20,h21,?_⟩
  · intro x hx
    let xx : B := ⟨x,hx⟩
    exact (hk (b xx * xx⁻¹)).mp (by rw [map_mul,map_inv,hfix,mul_inv_cancel])
  · intro x
    have hsid : σ.toRingHom = RingHom.id E := by rw [hσ]; rfl
    simpa only [hsid, GeneralLinearGroup.map_id, MonoidHom.id_apply] using hu x
/-- Cubic displacement makes a two-power special-unitary actor root inner. -/
theorem special_standard_borel_actor_mem_root_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hcore : (specialBorel J hJ).pCoreIn 2 = specialRoot J hJ)
    (A : Subgroup (MulAut (J.specialSubgroup)))
    (hA : IsPGroup 2 A) (hRA : (specialRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut (J.specialSubgroup)) (ha : a ∈ A)
    (hroot : (specialRoot J hJ).map a.toMonoidHom = specialRoot J hJ)
    (hc : ∀ x ∈ specialBorel J hJ, (a x * x⁻¹)^3 ∈ specialRoot J hJ) :
    a ∈ (specialRoot J hJ).map MulAut.conj := by
  obtain ⟨_,u,h10,h20,h21,hu⟩ := special_standard_borel_rigidity J hJ hn hcard hconj
    hcore a hroot hc
  exact SemilinearActors.special_identity_field_mem_root_inner J hJ hcard
    (by omega) A hA hRA a ha u h10 h20 h21 hu

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
