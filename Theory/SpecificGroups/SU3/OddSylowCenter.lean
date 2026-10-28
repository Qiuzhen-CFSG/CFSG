module
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Generators
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Order
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import ABG.ChapterII.Section1.SemidihedralGenerators
/-!
# Sylow centers for odd ternary unitary groups

For p congruent to one modulo four, the literal hyperbolic rotation and
swap generate a Sylow two-subgroup, as their order attains the proved
two-part bound. Its semidihedral presentation gives center of order two.
Sylow conjugacy and Hermitian basis transport retain arbitrary Sylows and
the original stored form. No simplicity or automorphism hypothesis is used.
Source: ABG II.2 Lemma 1; Aschbacher–Smith E.2.2(2d), pp.215–216.
-/
public section
noncomputable section
open Subgroup Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddSylowCenter
open CyclicCoreSylow OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] [Finite F]

/-- The center of every actual Sylow two-subgroup has order two in the
semidihedral unitary congruence, with no simplicity premise. -/
theorem card_center_standard (J : HermitianForm 3 F)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:p%4=1)
    (hcard:Nat.card F=p^2) (hc:∀x,J.conj x=x^p)
    (hJ:J.form=!![0,0,1;0,1,0;1,0,0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (center S)=2 := by
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨n,hd,hn⟩ := exists_parameter hp hm
  obtain ⟨x,y,hx,hy,hyx,_,_⟩ := exists_generators J hJ hp ho hcard hc n hd hn
  have hne : x^(2^(n+2)-1)≠x := by
    intro he
    have h4 : 4≤2^(n+2) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤n+2)
    have horder : orderOf x=2^(n+2)*2 := by rw [hx];ring
    have h := pow_injOn_Iio_orderOf (x:=x)
      (show 2^(n+2)-1<orderOf x by rw [horder];omega)
      (show 1<orderOf x by rw [horder];omega) (by simpa only [pow_one] using he)
    omega
  have hout : y∉zpowers x := by
    rintro ⟨i,rfl⟩
    apply hne
    rw [← hyx,(Commute.zpow_self x i).eq,mul_inv_cancel_right]
  obtain ⟨hsize,hshape,_⟩ := ABG.semidihedral_generated_subgroup_data
    (by omega : 2≤n+2) x y (by simpa only [Nat.add_assoc] using hx) hy hout hyx
  let Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toSubgroup := zpowers x⊔zpowers y
      isPGroup' := IsPGroup.of_card hsize
      is_maximal' := fun {R} hR hQR=>
        (Subgroup.eq_of_le_of_card_ge hQR (by
          rw [hsize]
          exact two_subgroup_card_le J hJ hp ho hcard hc n hd hn R hR)).symm }
  rw [← Nat.card_congr (Subgroup.centerCongr (Q.equiv S)).toEquiv]
  exact ABG.QuasiDihedral.card_center hshape

/-- Arbitrary stored Hermitian forms retain the same actual Sylow-center order. -/
theorem card_center (J : HermitianForm 3 F)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:p%4=1)
    (hcard:Nat.card F=p^2) (hc:∀x,J.conj x=x^p)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (center S)=2 := by
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let _ : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x:F // J.conj x=x}=p := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
      (by decide) (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hc)
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  let S' := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eS : S≃*S' := (S:Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  rw [Nat.card_congr (Subgroup.centerCongr eS).toEquiv]
  exact card_center_standard (FormTransport.standardForm J) hp ho hm hcard hc rfl S'
end BenderSuzuki.MatrixGroups.HermitianForm.OddSylowCenter
