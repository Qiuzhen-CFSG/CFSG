module
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Generators
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Order
public import Theory.GroupTheory.SemidihedralSixteenPair
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# The actual semidihedral Sylow subgroup of PSU₃(5)

The hyperbolic torus and Weyl element have orders eight and two, with
conjugation acting by the cube. Their generated subgroup has order sixteen,
which is the complete two-part of the projective unitary order. Sylow
conjugacy and Hermitian form transport give the same presentation for every
supplied Sylow subgroup, without a simplicity or abstract model premise.

Source: Aschbacher--Smith A.3.21(b), printed p.55, and E.1.14(7), p.214;
Alperin--Brauer--Gorenstein II.2 Lemma 1, article p.17.
-/

public noncomputable section
open Matrix Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] [Finite F]

private theorem standard_sylow (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hF : Nat.card F = 5^2) (hc : ∀ x, J.conj x = x^5)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card S = 16 ∧ Stellmacher.IsSemidihedralGroup S := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨x,y,hx,hy,hyx,_,_⟩ := CyclicCoreSylow.exists_generators J hJ
    (by decide : Nat.Prime 5) (by decide) hF hc 0 (by decide) (by decide)
  have hx8 : orderOf x = 8 := by simpa using hx
  have hy3 : y*x*y⁻¹=x^3 := by simpa using hyx
  have hyne : y ≠ 1 := by
    intro he
    have he3 : x^3=x := by simpa only [he,one_mul,inv_one,mul_one] using hy3.symm
    have he2 : x^2=1 := mul_right_cancel
      (show x^2*x=1*x by simpa only [←pow_succ,one_mul] using he3)
    have hd := orderOf_dvd_of_pow_eq_one he2
    rw [hx8] at hd
    norm_num at hd
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy hyne
  obtain ⟨hcard,hshape⟩ := Semidihedral.sixteen_of_pair x y hx8 hy2 hy3
  let H := zpowers x ⊔ zpowers y
  have hH : IsPGroup 2 H := IsPGroup.of_card (n := 4) hcard
  let Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toSubgroup := H
      isPGroup' := hH
      is_maximal' := fun {R} hR hHR =>
        (eq_of_le_of_card_ge hHR (by
          rw [hcard]
          exact CyclicCoreSylow.two_subgroup_card_le J hJ (by decide : Nat.Prime 5)
            (by decide) hF hc 0 (by decide) (by decide) R hR)).symm }
  exact ⟨(Nat.card_congr (Q.equiv S).toEquiv).symm.trans hcard,
    Semidihedral.of_mulEquiv (Q.equiv S) hshape⟩

/-- Every literal Sylow two-subgroup of PSU₃(5) is semidihedral of order sixteen. -/
theorem sylow_semidihedral (J : HermitianForm 3 F)
    (hF : Nat.card F = 5^2) (hc : ∀ x, J.conj x = x^5)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card S = 16 ∧ Stellmacher.IsSemidihedralGroup S := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x=x}=5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 5 hF hf
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hcS,hsS⟩ := standard_sylow (FormTransport.standardForm J) rfl hF hc S'
  let d : S ≃* S' := (S : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨(Nat.card_congr d.toEquiv).trans hcS,Semidihedral.of_mulEquiv d.symm hsS⟩

/-- The supplied Sylow retains explicit order-eight and involution generators. -/
theorem sylow_generators (J : HermitianForm 3 F)
    (hF : Nat.card F = 5^2) (hc : ∀ x, J.conj x = x^5)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ a b : S, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set S)=⊤ := by
  obtain ⟨hcS,n,hn,hcard,a,b,ha,hb,hab,hgen⟩ := sylow_semidihedral J hF hc S
  have hn4 : n=4 := by
    have he : 2^n=2^4 := by rw [←hcard,hcS]; norm_num
    exact (Nat.pow_right_injective (by decide : 1<2)) he
  exact ⟨a,b,by simpa [hn4] using ha,hb,by simpa [hn4] using hab,hgen⟩
end BenderSuzuki.MatrixGroups.HermitianForm.FiveSylow
