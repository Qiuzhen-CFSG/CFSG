module
public import Theory.Representation.DegreeThreeFrattini
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.OddClassicalSylowFrattini

/-!
# Three Frattini generators in determinant-one degree three

For a finite two-group represented faithfully in odd characteristic and degree
three, the weight action puts a self-centralizing normal abelian subgroup at
index at most two. Determinant one bounds its omega subgroup by four, so the
Frattini quotient has at most eight elements. The actual projective linear and
unitary quotients inherit this bound through their original quotient maps.

This supplies the GL₄(2) outer-section exclusion in Aschbacher--Smith 4.4.10--11
and 12.1.9, printed pp.621 and 793.
-/

public section
open scoped IsMulCommutative TensorProduct MatrixGroups
open Subgroup
namespace Theory.SpecificGroups.OddThreeFrattini
open Representation
variable {F P : Type*} [Field F] [Group P] [Finite P]

/-- The determinant-one hypothesis removes the fourth possible Frattini generator. -/
theorem card_le_eight (hP : IsPGroup 2 P) (j : P →* GL (Fin 3) F)
    (hj : Function.Injective j) (h2 : (2 : F) ≠ 0)
    (hdet : ∀ x, Matrix.GeneralLinearGroup.det (j x) = 1) :
    Nat.card (P ⧸ frattini P) ≤ 8 := by
  let rho : Representation F P (Fin 3 → F) := (Representation.generalLinearNatural 3).comp j
  have hrho : Function.Injective rho := (Representation.generalLinearNatural_injective 3).comp hj
  have hdim : Module.finrank F (Fin 3 → F) ≤ 3 := by simp
  classical
  obtain ⟨A, hAn, hAc, hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let E := AlgebraicClosure F
  let sigma := rho.extendScalars E
  have hsigma : Function.Injective sigma :=
    (extendScalars_faithful_iff E rho).mp hrho
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  have horderAE : (Nat.card A : E) ≠ 0 := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup A).exists_card_eq
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ h2E
  have hdimE : Module.finrank E (E ⊗[F] (Fin 3 → F)) ≤ 3 := by
    simpa only [Module.finrank_baseChange] using hdim
  obtain ⟨hfinite, hweights⟩ :=
    characterWeight_card_le (sigma.comp A.subtype) horderAE
  let W := CharacterWeight (sigma.comp A.subtype)
  let : Finite W := hfinite
  let := Fintype.ofFinite W
  let i : P →* Subgroup.normalizer (A : Set P) :=
    (MonoidHom.id P).codRestrict _ (fun g => by
      rw [A.normalizer_eq_top]
      trivial)
  let f : P →* Equiv.Perm W :=
    ((automizerWeightPerm sigma A).comp A.normalizerMonoidHom.rangeRestrict).comp i
  have hker : f.ker = A := by
    have h := normalizerWeightPerm_ker sigma A hsigma horderAE
    ext g
    change i g ∈ ((automizerWeightPerm sigma A).comp
      A.normalizerMonoidHom.rangeRestrict).ker ↔ g ∈ A
    rw [h]
    change g ∈ Subgroup.centralizer (A : Set P) ↔ g ∈ A
    exact ⟨fun h => hCA h, fun h => A.le_centralizer h⟩
  have hdiv : A.index ∣ (Nat.card W).factorial := by
    rw [← hker, Subgroup.index_ker]
    have hd := f.range.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hd
  have hdiv6 : A.index ∣ 6 :=
    hdiv.trans (Nat.factorial_dvd_factorial (hweights.trans hdimE))
  have hidx6 : A.index ≤ 6 := by
    exact Nat.le_of_dvd (by decide) hdiv6
  obtain ⟨n, hncard⟩ := hP.index A
  have hnlt : n < 3 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hncard] at hh'
    norm_num at hh'
    omega
  have hi2 : A.index ≤ 2 := by
    rw [hncard] at hdiv6 ⊢
    interval_cases n <;> norm_num at *
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  let k := (j.comp A.subtype).comp O.subtype
  have hO : Nat.card O ≤ 4 := OddThreeRank.elementary_card_le_four k
    ((hj.comp A.subtype_injective).comp O.subtype_injective) h2
    (fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 O) x)
    (fun x => hdet x.val.val)
  exact (hP.card_frattini_quotient_le_index_mul_omega_one A).trans
    (by simpa using Nat.mul_le_mul hi2 hO)

/-- The projective linear bound uses the literal special-linear cover. -/
theorem projective_linear [Finite F] (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 PSL(3,F)) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  apply OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(3,F))) (QuotientGroup.mk'_surjective _) ?_ P
  intro Q
  exact card_le_eight Q.isPGroup'
    (Matrix.SpecialLinearGroup.toGL.comp (Q : Subgroup SL(3,F)).subtype)
    (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective) h2
    (fun x => Matrix.SpecialLinearGroup.coeToGL_det x.val)

/-- The unitary bound retains the stored Hermitian form and its projective map. -/
theorem projective_unitary [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 8 := by
  apply OddClassicalSylowFrattini.card_le_of_surjective
    (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup) ?_ P
  intro Q
  exact card_le_eight Q.isPGroup'
    (J.specialSubgroup.subtype.comp (Q : Subgroup J.specialSubgroup).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) h2
    (fun x => x.val.property.2)

end Theory.SpecificGroups.OddThreeFrattini
