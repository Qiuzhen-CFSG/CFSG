module
public import Theory.SpecificGroups.SU3.EvenBorelCubicAction
public import Theory.FieldTheory.NinthDisplacement
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors
/-!
# Cubic rigidity above the exceptional unitary degree three

The projective torus has cubic kernel. Cubic displacement on the full
Borel quotient therefore gives ninth-power displacement of coefficient
units. If the binary degree exceeds three, additive spanning forces the
field automorphism to be identity. A two-power actor in a two-subgroup
containing the marked root inner image is then itself root inner.

The degree-three case is retained: over GF(64), the quadratic field
automorphism has ninth-power displacement, so this argument does not
remove that parameter. Source: Aschbacher--Smith 12.6.31, pp.836--837.
-/
public section
open Subgroup Matrix BenderSuzuki.External Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Cubic displacement on the full Borel quotient vanishes above binary degree three. -/
theorem large_standard_borel_rigidity
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 3 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hcore : (projectiveBorel J hJ).pCoreIn 2 = projectiveRoot J hJ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hc : ∀ x ∈ projectiveBorel J hJ, (a x * x⁻¹)^3 ∈ projectiveRoot J hJ) :
    (∀ x ∈ projectiveBorel J hJ, a x * x⁻¹ ∈ projectiveRoot J hJ) ∧
    ∃ u : J.unitarySubgroup, u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧
      u.val.val 2 1 = 0 ∧
      ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        (a x).val = ProjGenLinGroup.mk u.val * x.val *
          (ProjGenLinGroup.mk u.val)⁻¹ := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2^n) hq hcard hfixed
  obtain ⟨σ,u,hu⟩ := EvenSemilinear.semilinear_coverage J hJ (by omega) hcard hconj a
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
  have hker (k : Eˣ) (hkf : f k = 1) : k^3 = 1 := by
    have hr : hermitianTorusPSU J hJ k ∈ R := (hk (t k)).mp hkf
    have hone := Subgroup.disjoint_def.mp
      (SemilinearActors.projective_root_disjoint_torus J hJ) hr
      (show hermitianTorusPSU J hJ k ∈ projectiveTorus J hJ from ⟨_,rfl⟩)
    exact ((projective_eq_one_iff J hJ k).mp hone).2
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
    apply FiniteField.eq_one_of_unit_displacement_ninth
      (q := 2^n) (by
        have h16 : 2^4 ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
        norm_num at h16 ⊢
        omega) hcard σ
    intro k
    have hcub : f ((Units.map σ.toMonoidHom k * k⁻¹)^3) = 1 := by
      rw [map_pow,map_mul,map_inv,←hact]
      change (π (b (t k)) * (π (t k))⁻¹)^3 = 1
      rw [←map_inv,←map_mul,←map_pow]
      exact (hk _).mpr (hc (t k) (t k).property)
    simpa only [←pow_mul] using hker _ hcub
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
    simpa only [hsid, ProjGenLinGroup.map_id, MonoidHom.id_apply] using hu x
/-- A two-power actor with cubic Borel displacement is root inner
when the binary field degree exceeds three. -/
theorem large_standard_borel_actor_mem_root_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 3 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hcore : (projectiveBorel J hJ).pCoreIn 2 = projectiveRoot J hJ)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : IsPGroup 2 A) (hRA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hc : ∀ x ∈ projectiveBorel J hJ, (a x * x⁻¹)^3 ∈ projectiveRoot J hJ) :
    a ∈ (projectiveRoot J hJ).map MulAut.conj := by
  obtain ⟨_,u,h10,h20,h21,hu⟩ := large_standard_borel_rigidity J hJ hn hcard hconj
    hcore a hroot hc
  exact SemilinearActors.projective_identity_field_mem_root_inner J hJ hcard
    (by omega) A hA hRA a ha u h10 h20 h21 hu

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
