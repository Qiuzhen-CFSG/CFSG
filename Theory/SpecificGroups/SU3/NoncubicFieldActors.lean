module
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import Theory.SpecificGroups.SU3.ExtensionBorel.Actors
public import Theory.SpecificGroups.SU3.BorelCoprimeFieldAction
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.Coordinates
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.FieldTheory.PrimeOrderFixedUnits
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.SU3.NoncubicPrimeRank
public import Theory.GroupAction.ComponentRankAction.ResidualSource

/-!
# Noncubic field actors in binary unitary components

Semilinear coverage and the cyclic diagonal outer group of order dividing
three give an inner-field factorization of every p-power actor for p > 3.
A basis change over F₂ converts the antidiagonal Hermitian form to the
identity. The two norm-one torus directions then survive in the fixed group
of a field actor of order p. Their faithful inner image together with the
outer actor forces rank three.

Consequently a component of rank two and p-prime center absorbs every
ambient p-element when its central quotient is PSU₃(2ⁿ), n ≥ 2. This keeps
the original component and covers central three-extensions. Simplicity is
inherited from that component. The literal source application is in
NonblockEndgameSieveModelsNoncubicUnitary.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.12(2), p.617;
GLS3 Theorem 2.5.12 and §2.7 for the imported semilinear matrix model.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors
open ExtensionBorel
variable {F : Type*} [Field F] [Finite F]
variable (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
variable {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
variable (hconj : ∀ x, J.conj x = x^(2^n))

private theorem field_form (σ : F ≃+* F) :
    J.HasUnitarySemilinearForm (fieldActorHom J hJ σ) σ := by
  refine ⟨1,fun x => ?_⟩
  simp only [fieldActorHom,MonoidHom.coe_mk,OneHom.coe_mk,fieldActor_apply_val]
  change ProjGenLinGroup.map σ.toRingHom x.val =
    ProjGenLinGroup.mk 1 * _ * (ProjGenLinGroup.mk 1)⁻¹
  simp

include hn hcard hconj in
/-- A pure coefficient actor cannot be inner unless its coefficient is trivial. -/
theorem field_eq_one_of_inner (σ : F ≃+* F)
    (hi : fieldActorHom J hJ σ ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : σ = 1 := by
  obtain ⟨g,hg⟩ := hi
  obtain ⟨x,rfl⟩ := J.specialToProjective_surjective g
  have hinner : J.HasUnitarySemilinearForm (fieldActorHom J hJ σ) 1 :=
    (HasUnitarySemilinearForm.one_iff J).mpr
      ⟨⟨x.val,x.property.1⟩, hg.symm.trans (J.unitaryConj_special_is_inner x).symm⟩
  have hh := (hinner.inv J hJ).mul J hJ (field_form J hJ σ)
  rw [inv_mul_cancel,inv_one,one_mul] at hh
  exact J.semilinear_identity_field_eq_one n hn hJ hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj) σ hh

include hn hcard hconj in
/-- The coefficient action is faithful on the actual projective carrier. -/
theorem fieldActor_injective : Function.Injective (fieldActorHom J hJ) := by
  apply (fieldActorHom J hJ).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro σ hσ
  apply mem_bot.mpr
  apply field_eq_one_of_inner J hJ hn hcard hconj σ
  rw [show fieldActorHom J hJ σ = 1 from hσ]
  exact (MulAut.innerSubgroup _).one_mem

/-- The cyclic diagonal outer image has order dividing three. -/
theorem diagonalOuter_card_dvd_three : Nat.card J.unitaryOuterHom.range ∣ 3 := by
  let := J.unitaryOuterHom_range_isCyclic
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  rintro ⟨_,u,rfl⟩
  apply Subtype.ext
  change J.unitaryOuterHom u ^ 3 = 1
  simp only [unitaryOuterHom,MonoidHom.comp_apply,unitaryConjHom_apply]
  rw [← map_pow]
  obtain ⟨g,hg⟩ := J.unitaryConj_cube_is_inner u
  rw [hg]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩

include hn hcard hconj in
/-- Every noncubic prime-power actor has a genuine inner-field factorization. -/
theorem inner_field_of_primePower
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p m : ℕ} [Fact p.Prime] (hp : 3 < p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^(p^m)=1) :
    ∃ (g : ProjectiveSpecialUnitaryMatrixGroup J) (σ : F ≃+* F),
      a = MulAut.conj g * fieldActorHom J hJ σ ∧ σ^(p^m)=1 := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hcover := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj
  obtain ⟨σ,hform⟩ := hcover a
  have hs := BorelCoprimeFieldAction.coefficient_pow J hJ hn hcard hconj hform ha
  obtain ⟨u,hu⟩ := hform
  have he : a = J.unitaryConj u * fieldActorHom J hJ σ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a x).val = (J.unitaryConj u (fieldActorHom J hJ σ x)).val
    rw [J.unitaryConj_apply_val,hu]
    simp only [fieldActorHom,MonoidHom.coe_mk,OneHom.coe_mk,fieldActor_apply_val]
  let D := J.unitaryOuterHom.range
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let := J.unitaryOuterHom_range_isCyclic
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  have hqu : J.unitaryOuterHom u = q (J.unitaryConj u) := by
    simp only [unitaryOuterHom,MonoidHom.comp_apply,unitaryConjHom_apply,q]
  let b : normalizer (D : Set _) := ⟨q a,by rw [D.normalizer_eq_top]; trivial⟩
  have hb : b^(p^m)=1 := by
    apply Subtype.ext
    change q a ^ (p^m)=1
    rw [←map_pow,ha,map_one]
  have hc : Nat.Coprime (p^m) (Nat.card (MulAut D)) := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_three).mp (diagonalOuter_card_dvd_three J) with h | h
    · change Nat.card D = 1 at h
      rw [h]
      simp
    · change Nat.card D = 3 at h
      rw [h]
      change Nat.Coprime (p^m) 2
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by decide : 0 < 2) hd
        omega)).pow_left m
  have hact : D.normalizerMonoidHom b = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    have h₁ := orderOf_dvd_of_pow_eq_one (show D.normalizerMonoidHom b ^ (p^m)=1 by
      rw [←map_pow,hb,map_one])
    have h₂ := orderOf_dvd_natCard (D.normalizerMonoidHom b)
    simpa only [hc.gcd_eq_one] using Nat.dvd_gcd h₁ h₂
  have hucomm : Commute (q a) (J.unitaryOuterHom u) := by
    have hh := congrArg (fun k : MulAut D => k ⟨J.unitaryOuterHom u,⟨u,rfl⟩⟩) hact
    have heq : q a * J.unitaryOuterHom u * (q a)⁻¹ = J.unitaryOuterHom u :=
      congrArg Subtype.val hh
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hcomm : Commute (J.unitaryOuterHom u) (q (fieldActorHom J hJ σ)) := by
    rw [hqu]
    rw [hqu] at hucomm
    have hh := hucomm.eq
    change q a * q (J.unitaryConj u) = q (J.unitaryConj u) * q a at hh
    rw [he,map_mul] at hh
    exact (mul_left_cancel (by simpa only [mul_assoc] using hh)).symm
  have hup : J.unitaryOuterHom u ^ (p^m)=1 := by
    have hh := congrArg q ha
    rw [he,map_pow,map_mul,map_one,←hqu,hcomm.mul_pow] at hh
    have hf : q (fieldActorHom J hJ σ)^(p^m)=1 := by
      rw [←map_pow,←map_pow,hs,map_one,map_one]
    rwa [hf,mul_one] at hh
  have hu3 : J.unitaryOuterHom u ^ 3=1 := by
    obtain ⟨g,hg⟩ := J.unitaryConj_cube_is_inner u
    rw [hqu]
    rw [←map_pow,hg]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  have huo : J.unitaryOuterHom u = 1 := by
    apply orderOf_eq_one_iff.mp
    have hc3 : Nat.Coprime (p^m) 3 :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by decide : 0 < 3) hd
        omega)).pow_left m
    exact Nat.eq_one_of_dvd_coprimes hc3
      (orderOf_dvd_of_pow_eq_one hup) (orderOf_dvd_of_pow_eq_one hu3)
  rw [hqu] at huo
  obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp huo
  exact ⟨g,σ,he.trans (congrArg (fun b => b * fieldActorHom J hJ σ) hg.symm),hs⟩
end BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors
open ExtensionBorel UnitaryThree.OddTorusNormalizer EvenInner
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def binaryBasis : GL (Fin 3) F := {
  val := !![1,0,1;1,1,1;0,1,1]
  inv := !![0,1,1;1,1,0;1,1,1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero] }

private def binaryFrame : OrthogonalFrame J := ⟨binaryBasis, by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryBasis,HermitianForm.conjTranspose,hJ,Matrix.mul_apply,
      Fin.sum_univ_three,CharTwo.add_self_eq_zero]⟩

omit [Finite F] in
private theorem binaryBasis_map (σ : F ≃+* F) :
    GeneralLinearGroup.map σ.toRingHom (binaryBasis (F := F)) = binaryBasis := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryBasis,GeneralLinearGroup.map]

variable {p : ℕ} [Fact p.Prime]

/-- A prime-order field actor fixes both norm-one torus directions away from three. -/
theorem field_fixed_rank (σ : F ≃+* F) (hσ : orderOf σ = p)
    {q : ℕ} (_hq : 1 < q) (hcard : Nat.card F = q^2)
    (hconj : ∀ x, J.conj x = x^q) (hp3 : p ≠ 3) (hd : p ∣ q+1) :
    2 ≤ primeRank p (fieldActorHom J hJ σ).fixedSubgroup := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hsplit : p ∣ Nat.card F - 1 := by
    rw [hcard,show q^2-1 = (q+1)*(q-1) by simpa using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_left hd _
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' p
    (FiniteField.prime_dvd_fixed_units σ hσ hsplit)
  let j : (FixedBy.subfield F σ)ˣ →* Fˣ :=
    Units.map (FixedBy.subfield F σ).subtype.toMonoidHom
  have hj : Function.Injective j := by
    intro a b hh
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hh
  let C := zpowers (j t)
  have hCcard : Nat.card C = p := by
    rw [Nat.card_zpowers,orderOf_injective j hj,ht]
  have hnorm : C ≤ normOne J := by
    apply zpowers_le.mpr
    rw [normOne_eq_rootsOfUnity J hconj,mem_rootsOfUnity]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [orderOf_injective j hj,ht]
    exact hd
  have hfix (a : C) : Units.map σ.toMonoidHom a.val = a.val := by
    obtain ⟨k,hk⟩ := a.property
    rw [← hk,map_zpow]
    congr 1
    apply Units.ext
    exact (t.val).property
  let g : C × C →* J.specialSubgroup :=
    (specialPairHom J (binaryFrame J hJ)).comp
      ((inclusion hnorm).prodMap (inclusion hnorm))
  have hg : Function.Injective g :=
    (specialPairHom_injective J (binaryFrame J hJ)).comp
      (fun _ _ he => Prod.ext
        (inclusion_injective hnorm (congrArg Prod.fst he))
        (inclusion_injective hnorm (congrArg Prod.snd he)))
  have hgfix (x : C × C) : GeneralLinearGroup.map σ.toRingHom (g x).val = (g x).val := by
    change GeneralLinearGroup.map σ.toRingHom
      (binaryBasis * diagonalHom (pairDiagonal J _) * binaryBasis⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryBasis_map]
    congr 2
    apply Units.ext
    ext i k
    by_cases hik : i=k
    · subst k
      fin_cases i <;>
        simp [diagonalHom,pairDiagonal,GeneralLinearGroup.map,
          show σ (x.1.val : F) = (x.1.val : F) from congrArg Units.val (hfix x.1),
          show σ (x.2.val : F) = (x.2.val : F) from congrArg Units.val (hfix x.2)]
    · simp [diagonalHom,GeneralLinearGroup.map,hik]
  let f : C × C →* (fieldActorHom J hJ σ).fixedSubgroup :=
    (J.specialToProjective.comp g).codRestrict _ (fun x => by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      simp only [fieldActorHom,MonoidHom.coe_mk,OneHom.coe_mk,fieldActor_apply_val,
        MonoidHom.comp_apply,specialToProjective_apply_val]
      rw [ProjGenLinGroup.map_mk,hgfix])
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    let k : f.ker →* J.specialToProjective.ker :=
      (g.comp f.ker.subtype).codRestrict _ (fun x => by
        exact congrArg Subtype.val x.property)
    have hki : Function.Injective k := by
      intro a b he
      exact Subtype.ext (hg (congrArg Subtype.val he))
    have hkd : Nat.card f.ker ∣ 3 :=
      (card_dvd_of_injective k hki).trans J.card_specialToProjective_ker_dvd_three
    exact Nat.Coprime.of_dvd_right hkd
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hh =>
        hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hh)))
  have hCrank : 1 ≤ primeRank p C := by
    by_contra hn
    have hz : primeRank p C = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by rw [hCcard])
  have hr := primeRank_le_of_coprime_ker p f hk
  rw [primeRank_prod_eq_add] at hr
  omega
end BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors

namespace BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open ExtensionBorel
variable {F : Type*} [Field F] [Finite F]
variable (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
variable {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
variable (hconj : ∀ x, J.conj x = x^(2^n))
variable {p : ℕ} [Fact p.Prime]

include hn hcard hconj in
private theorem field_actor_rank_three (hp3 : p ≠ 3)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hinner : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ=p) (hσA : fieldActorHom J hJ σ ∈ A)
    (hd : p ∣ 2^n+1) : 3 ≤ primeRank p A := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2) (by
    simpa only [←Nat.card_eq_fintype_card,pow_mul] using hcard)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hr := field_fixed_rank J hJ σ hσ (one_lt_pow₀ (by decide) (by omega)) hcard hconj hp3 hd
  obtain ⟨B,hB,hcB⟩ := exists_elementaryAbelian_card_primeRank
    (G := (fieldActorHom J hJ σ).fixedSubgroup) (p := p)
  let := hB
  obtain ⟨C,hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) p
    (n := 2) (by rw [hcB]; exact pow_dvd_pow p hr)
  let : IsElementaryAbelian p C := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun c => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p B) c.val) }
  let j := (fieldActorHom J hJ σ).fixedSubgroup.subtype.comp B.subtype
  let E := C.map j
  let : IsElementaryAbelian p E := IsElementaryAbelian.map j
  have hj : Function.Injective j :=
    (fieldActorHom J hJ σ).fixedSubgroup.subtype_injective.comp B.subtype_injective
  have hEc : Nat.card E = p^2 := by rw [card_map_of_injective hj,hC]
  have hfix : E ≤ (fieldActorHom J hJ σ).fixedSubgroup := by
    rintro _ ⟨c,_,rfl⟩
    exact c.val.property
  let f : ProjectiveSpecialUnitaryMatrixGroup J →* A :=
    MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (MulAut.conj_injective_of_center_eq_bot
      (EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj))
      (congrArg Subtype.val hh)
  let U := E.map f
  let : IsElementaryAbelian p U := IsElementaryAbelian.map f
  let x : A := ⟨fieldActorHom J hJ σ,hσA⟩
  have hx : orderOf x=p := by
    rw [←orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective (fieldActorHom J hJ)
      (fieldActor_injective J hJ hn hcard hconj) σ).trans hσ
  have hxU : x ∉ U := by
    rintro ⟨g,_,he⟩
    have hs := field_eq_one_of_inner J hJ hn hcard hconj σ ⟨g,congrArg Subtype.val he⟩
    rw [hs,orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hUfix : U ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * (fieldActorHom J hJ σ) y * g⁻¹ = (fieldActorHom J hJ σ) (g*y*g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcU : Nat.card U = p^2 := by rw [card_map_of_injective hf,hEc]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join U x hx hxU hUfix hcU

include hJ hn hcard hconj in
/-- Noncubic prime-power actors in the standard unitary model are inner at rank two. -/
theorem standard_inner_of_primePower
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hp : 3 < p) (hd : p ∣ 2^n+1)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hinner : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ A)
    (hrank : primeRank p A ≤ 2)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (haA : a ∈ A)
    (ha : ∃ m : ℕ, a^(p^m)=1) :
    a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he,hσ⟩ := inner_field_of_primePower J hJ hn hcard hconj hp a ham
  have hσA : fieldActorHom J hJ σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hσone : σ=1 := by
    by_contra hnσ
    have hP : IsPGroup p (zpowers σ) := IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
    have hdP : p ∣ Nat.card (zpowers σ) := hP.card_eq_or_dvd.resolve_left (by
      intro hc
      have hb := (card_eq_one.mp hc : zpowers σ = ⊥)
      exact hnσ (mem_bot.mp (hb ▸ mem_zpowers σ)))
    obtain ⟨τ,hτ⟩ := exists_prime_orderOf_dvd_card' p hdP
    have hτA : fieldActorHom J hJ (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [←hk,map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F)=p :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := field_actor_rank_three J hJ hn hcard hconj (by omega) A hinner τ hτp hτA hd
    omega
  rw [he,hσone,map_one,mul_one]
  exact ⟨g,rfl⟩

include hn hcard hconj in
/-- Genuine Hermitian basis change preserves the original actor subgroup and rank bound. -/
theorem inner_of_primePower
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hp : 3 < p) (hd : p ∣ 2^n+1)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hinner : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ A)
    (hrank : primeRank p A ≤ 2)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (haA : a ∈ A)
    (ha : ∃ m : ℕ, a^(p^m)=1) :
    a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hfixed
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.isSimpleGroup_congr.mp inferInstance
  let c := MulAut.congr e
  let B := A.map c.toMonoidHom
  have hB : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) ≤ B := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hinner
  have hrB : primeRank p B ≤ 2 := by
    rw [←primeRank_equiv p (A.equivMapOfInjective c.toMonoidHom c.injective)]
    exact hrank
  have hb := standard_inner_of_primePower J₀ rfl hn hcard hconj hp hd B hB hrB (c a)
    (mem_map_of_mem _ haA) (by
      obtain ⟨k,hk⟩ := ha
      exact ⟨k,by rw [←map_pow,hk,map_one]⟩)
  rw [←MulAut.map_innerSubgroup_congr e] at hb
  obtain ⟨b,hb,he⟩ := hb
  exact c.injective he ▸ hb

include hn hcard hconj in
/-- The full component absorbs all ambient p-elements, including for a central three-cover. -/
theorem component_eq_primeClosure_and_residual
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hL : IsComponent G L)
    (hp : 3 < p) (hz : Nat.Coprime p (Nat.card (center L)))
    (hr : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    L = closure {x : G | orderOf x=p} ∧ L = primeToResidual p G := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.isSimpleGroup_congr.mp inferInstance
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hrmodel : 2 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [←primeRank_congr p e,←primeRank_eq_of_surjective_of_coprime p
      (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective (center L))
      (by rwa [QuotientGroup.ker_mk'])]
    exact hr
  have hd : p ∣ 2^n+1 := by
    by_contra hh
    have hpq : ¬p ∣ 2^n := fun hd => (by omega : p≠2)
      ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow hd))
    have hb := NoncubicPrimeRank.projective_rank_le_one J
      (one_lt_pow₀ (by decide) (by omega)) hcard
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj)
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hpq hh
    omega
  apply Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual hL hz hr hG e
  intro a ha m hm
  exact inner_of_primePower J hn hcard hconj hp hd _ (inner_le_range L e)
    (range_rank_le_two L e hz hr hG) a ha ⟨m,hm⟩
end BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors
