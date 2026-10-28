module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.RankTwoResidualExclusions
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeLocal
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLocal

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SquareFieldSections

/-!
# Excluding the placed rank-two components for the Hermitian quotient

The original perfect residual maps onto PSL₃(2^(2n)). Its literal inclusion
in a containing component, followed by the central quotient, has solvable
kernel and normalizes a nontrivial two-group. The nontrivial square excludes
the linear-Levi rows. Divisibility by three excludes the Ree Suzuki parabolic,
and divisibility by seven excludes both PSU₅(4) parabolics.

The concluding theorem applies to the placed component configuration with
its original residual and module. It includes n = 1. Selecting that
configuration and excluding the alternative pushing-up configuration remain
separate arguments, assembled on the chosen orbit in the Chapter 12 extension.
Source: Aschbacher--Smith 4.4.11--12, pp.621--622 (refs/quasithin.pdf).
-/

public noncomputable section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.Chapter4.Section04

namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian

private theorem no_seven_unitary_five_local
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (hseven : 7 ∣ Nat.card S)
    (π : A →* S) (hπ : Function.Surjective π)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 5 E)
    (hcard : Nat.card E = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J
  obtain ⟨W,hn,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J hJ (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J hcard hconj hJ W hn hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)).toMonoidHom := by
    rw [hg, Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hNW
  let j := (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).toMonoidHom.comp r
  have hj : j.range ≤ (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
      else Theory.SpecificGroups.UnitaryFive.lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hNW (hr ⟨x,rfl⟩)
    change (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹ * r x *
      ((Theory.SpecificGroups.UnitaryFive.project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).injective
        (he.trans (map_one _).symm))) (inclusion_injective _)
  have hd := hseven.trans (SimpleSection.card_dvd_of_solvable_representation hS π hπ k)
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] at hd
    norm_num at hd
  · simp only [↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] at hd
    norm_num at hd

private theorem no_rank_two_residual_of_three_seven
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (hthree : 3 ∣ Nat.card S) (hseven : 7 ∣ Nat.card S)
    (π : F →* S) (hπ : Function.Surjective π)
    (hr : 12 ≤ primeRank 2 (K ⧸ center K))
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) : False := by
  have hmodel := unitary_five_or_ree_of_residual_module F K W hFK hWF hne hcomm
    hS hexp π hπ hr hm
  rcases hmodel with h | ⟨m,hm,⟨e⟩⟩
  · obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := h
    have hc : Nat.card E = 16 := hcard
    let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hc
    obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hc hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact no_seven_unitary_five_local hS hseven π hπ
      (HermitianForm.IdentityGram.identityGram J) hc hconj rfl _ hp hpne r hnorm
  · let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_ree_local_of_three_dvd hS hexp hthree π hπ hm _ hp hpne r hnorm

private theorem no_rank_two_component_of_three_seven
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {L W A : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (hthree : 3 ∣ Nat.card S) (hseven : 7 ∣ Nat.card S)
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π)
    (hc : RankTwoComponentCase L W A S) : False := by
  obtain ⟨K,_,_,_,_,⟨n,hm⟩,_,hf,_,hr,_⟩ := hc
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let e : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  let : Group.IsPerfect (oddActorResidual L A) := oddActorResidual_isPerfect L A
  have hrJ : 12 ≤ primeRank 2 (J ⧸ center J) := by
    rwa [primeRank_equiv 2 z]
  exact no_rank_two_residual_of_three_seven (oddActorResidual L A) J W
    hf hWF hne hcomm hS hexp hthree hseven π hπ hrJ (hm.of_mulEquiv z)

/-- No placed rank-two component can contain the original residual and its
nontrivial commutator module with a square-field PSL₃ simple quotient. -/
theorem no_hermitian_rank_two_component
    {G S E : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    [Field E] [Finite E] [CharP E 2]
    {L W A : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hS : ¬ Group.IsSolvable S) (e : S ≃* PSL(3,E))
    {n : ℕ} (hcard : Nat.card E = 2 ^ (2*n))
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π) :
    ¬ RankTwoComponentCase L W A S :=
  no_rank_two_component_of_three_seven hWF hne hcomm hS
    (Matrix.PSL3.LinearThree.not_two_exponent e hcard)
    (Matrix.PSL3.LinearThree.square_three_dvd_card e hcard)
    (Matrix.PSL3.LinearThree.square_seven_dvd_card e hcard) π hπ

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
