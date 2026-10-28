module
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.SmallThreeCore
public import Theory.GroupTheory.PGroup.ExponentFourRankOne
public import Theory.Representation.AffineNine.QuaternionSource
/-!
# Binary obstruction in small projective unitary overgroups

The actual Sylow two-subgroups of PSU₃(2) are quaternion of order eight.
The Hermitian root square formula gives exponent four; two-rank one
and order eight then select Q₈ from the cyclic/quaternion alternatives.

If a finite group of order 72 or 144 with trivial two-core contains a
normal copy of PSU₃(2), the copy's characteristic three-core is a normal
elementary nine-group. An actual Sylow two-subgroup supplements it and
contains the original quaternion. Its faithful conjugation image supplies
the affine-nine cubic-ratio bound, on the original representation.

This applies to both possible small-projective enlargements in DGS,
Groups and Graphs (1985), 6.1 and 6.4--6.5, pp.118--122. It does not
assert that the order-144 enlargement is absent. The affine weight argument
is the quaternion obstruction used in Aschbacher--Smith 13.3.14(d), p.892.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
open OddPrimeSylow.NormalizedOuter.Coverage OddPrimeSylow.NormalizedOuter.FormTransport
variable {F : Type*} [Field F] [Finite F]
private instance (J : HermitianForm 3 F) : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

private theorem standard_sylow_quaternion (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x=x^2) :
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J), Nonempty (S ≃* QuaternionGroup 2) := by
  have hc' : Nat.card F = (2^1)^2 := by simpa using hc
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hc)
  have hfixed : Nat.card {x : F // J.conj x=x} = 2^1 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide) hc'
      (by simpa using hconj)
  let S := EvenTwoRank.rootSylow J hJ (n := 1) (by decide) hc' hfixed
  have hcard : Nat.card S = 8 := by
    change Nat.card (rootGroup J hJ) = 8
    simpa using rootGroup_card J hJ 2 hc (by simpa using hfixed)
  have hpow : ∀ x : S, x^4=1 := by
    rintro ⟨x,hx⟩
    obtain ⟨z,rfl⟩ := hx
    apply Subtype.ext
    change (root J hJ z)^4=1
    rw [←map_pow]
    have hz : z^4=1 := by
      rw [show 4=2*2 by decide,pow_mul]
      apply Subtype.ext
      rw [EvenInner.square_coordinates,EvenInner.square_coordinates]
      simp only [zero_mul]
      rfl
    rw [hz,map_one]
  have hr : primeRank 2 S ≤ 1 := by
    rw [←S.primeRank_eq]
    exact (EvenTwoRank.two_rank J (n := 1) (by decide) hc' (by simpa using hconj)).le
  have hfour : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≠ 4 := by
    intro E hE he
    have hb := (primeRank_le_iff_elementary_card_le S).mp hr E hE
    norm_num [he] at hb
  rcases S.isPGroup'.isCyclic_or_quaternion_two_of_no_elementary_four hpow hfour with hs | hs
  · let := hs
    obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
    have hd := orderOf_dvd_of_pow_eq_one (hpow x)
    rw [hx,hcard] at hd
    norm_num at hd
  · exact ⟨S,hs⟩

/-- Every actual Sylow two-subgroup of PSU₃(2) is quaternion of order eight. -/
theorem projective_sylow_quaternion (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x=x^2)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nonempty (S ≃* QuaternionGroup 2) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Nat.finite_of_card_ne_zero (by rw [FixedFieldTwo.card_projective J hc hconj]; decide)
  have hf : Nat.card {x : F // J.conj x=x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
      (by simpa using hc) (by simpa using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J 2 hc hf
  obtain ⟨T,⟨f⟩⟩ := standard_sylow_quaternion (standardForm J) rfl hc hconj
  let U := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let g : T ≃* U := (T : Subgroup _).equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  exact ⟨(S.equiv U).trans (g.symm.trans f)⟩
end BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore

namespace Representation.RankOne.QuadraticRecognition
open BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
open Representation.AffineNine Representation.BinaryOffender
variable {K V : Type*} [Group K] [Finite K]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The quaternion action excludes small cubic ratios for both possible two-core-free overgroups. -/
theorem psu3_two_normal_overgroup_cubic_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x=x^2)
    (I : Subgroup K) [I.Normal] (e : I ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hK : Nat.card K = 72 ∨ Nat.card K = 144) (hcore : pCore 2 K=⊥)
    (ρ : Representation (ZMod 2) K V) (hf : Function.Injective ρ) :
    2 < cubicRatio ρ := by
  let H := ProjectiveSpecialUnitaryMatrixGroup J
  let N := (pCore 3 I).map I.subtype
  let : N.Normal := inferInstanceAs (((pCore 3 I).map I.subtype).Normal)
  let f : pCore 3 I ≃* pCore 3 H := ((pCore 3 I).equivMapOfInjective
    e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr (pCore_map_iso 3 e))
  let g : N ≃* pCore 3 H := ((pCore 3 I).equivMapOfInjective
    I.subtype I.subtype_injective).symm.trans f
  obtain ⟨h9,hE,_⟩ := projective_core_structure J hc hconj
  let := hE
  let : IsElementaryAbelian 3 N := IsElementaryAbelian.of_injective g.toMonoidHom g.injective
  have hN : Nat.card N=9 := (Nat.card_congr g.toEquiv).trans h9
  let T : Sylow 2 I := Classical.choice inferInstance
  let TH := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨eT⟩ := projective_sylow_quaternion J hc hconj TH
  let eT' : T ≃* QuaternionGroup 2 :=
    ((T : Subgroup I).equivMapOfInjective e.toMonoidHom e.injective).trans eT
  obtain ⟨S,hTS⟩ := (T.isPGroup'.map I.subtype).exists_le_sylow
  have hNS : N.IsComplement' (S : Subgroup K) := by
    apply isComplement'_of_coprime
    · rw [hN,S.card_eq_multiplicity]
      rcases hK with hK | hK <;> rw [hK] <;> decide +kernel
    · rw [hN,S.card_eq_multiplicity]
      rcases hK with hK | hK <;> rw [hK] <;> decide +kernel
  have hcent := centralizer_eq_nine_of_twoCore_eq_bot N S S.isPGroup' hNS.sup_eq_top hcore
  let a := (MulAut.conjNormal : K →* MulAut N).comp (S : Subgroup K).subtype
  have hai : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro s hs
    have hsN : (s:K) ∈ N := by
      rw [←hcent,←MulAut.conjNormal_ker_eq_centralizer N]
      exact hs
    exact Subtype.ext (mem_bot.mp (hNS.disjoint.le_bot ⟨hsN,s.property⟩))
  let b : T →* S := (I.subtype.comp (T : Subgroup I).subtype).codRestrict (S : Subgroup K)
    (fun t => hTS (mem_map_of_mem I.subtype t.property))
  have hb : Function.Injective b := by
    intro t u he
    exact Subtype.ext (Subtype.ext (congrArg (fun s : S => (s:K)) he))
  let r := a.comp b
  let Q := r.range
  let eQ : Q ≃* QuaternionGroup 2 := (MonoidHom.ofInjective (f := r) (hai.comp hb)).symm.trans eT'
  have hQ : Q ≤ a.range := by
    rintro _ ⟨t,rfl⟩
    exact ⟨b t,rfl⟩
  exact cubicRatio_gt_two_of_normal_nine N S hN S.isPGroup' hNS.sup_eq_top hcent Q eQ hQ ρ hf
end Representation.RankOne.QuadraticRecognition
