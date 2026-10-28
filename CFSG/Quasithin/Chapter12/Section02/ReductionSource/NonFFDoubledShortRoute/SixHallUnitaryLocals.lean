module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryLie
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryLie
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Residual
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLocal

/-!
# The alternating-six residual in the full PSU₅(4) parabolics

The perfect residual kills the cubic character of the full line parabolic.
Its resulting projection has soluble kernel and SU₃(4) target, whose order
has only one factor three. In the full plane parabolic, perfectness places
it in the actual unipotent--SL₂ subgroup, and the projection to SL₂(F₁₆)
has two-group kernel. The original A₆ quotient survives these soluble
kernels, contradicting the line order or its order-four two-element.

All maps are on the actual normalizer of the residual two-core image.
No factor-seven argument, injective simple residual, or maximal-parabolic
normality assumption is used. Original Hall placement is a separate source
step.
Source: Aschbacher--Smith 4.4.12 and F.1.12(7), printed pp.622,263--264,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4.Section04.NormalizedRankOneOddControl
open Theory.SpecificGroups.UnitaryFive

private theorem no_six_line
    {A : Type*} [Group A] [Group.IsPerfect A]
    (hS : ¬ Group.IsSolvable (alternatingGroup (Fin 6)))
    (π : A →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (r : A →* lineParabolic J) [Group.IsSolvable r.ker] : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨c,hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let e := MulEquiv.ofBijective (LineCore.Parabolic.Blocks.fullMap J hconj c hc hJ)
    ⟨LineCore.Parabolic.Blocks.fullMap_injective J hconj c hc hJ,
      LineCore.Parabolic.Blocks.Exhaustion.fullMap_surjective J hconj hcard c hc hJ⟩
  let j := e.symm.toMonoidHom.comp r
  let : Group.IsSolvable j.ker := by
    change Group.IsSolvable (e.symm.toMonoidHom.comp r).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective]
    infer_instance
  let k := (LineCore.Parabolic.Blocks.productProjection J hconj).comp j
  let d := (LineCore.Parabolic.Blocks.productCharacter J hconj).comp j
  have hd (x : A) : d x = 1 :=
    Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
  let C := (SemidirectProduct.inl : LineCore.Coord J →*
    LineCore.Parabolic.Blocks.FullProduct J hconj).range
  have hp : IsPGroup 2 C := (LineCore.Coord.isPGroup (J := J)).of_surjective
    (SemidirectProduct.inl : LineCore.Coord J →*
      LineCore.Parabolic.Blocks.FullProduct J hconj).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  let : Finite (LineCore.Parabolic.Blocks.FullProduct J hconj) := Finite.of_equiv _ e.symm.toEquiv
  let : Group.IsNilpotent C := hp.isNilpotent
  have hk : k.ker = C.comap j := by
    ext x
    dsimp only [C]
    rw [← LineCore.Parabolic.Blocks.product_common_kernel]
    change k x = 1 ↔ k x = 1 ∧ d x = 1
    exact ⟨fun h => ⟨h,hd x⟩,And.left⟩
  let : Group.IsSolvable k.ker := by
    rw [hk]
    exact isSolvable_comap_of_solvable_ker j C
  have hdiv := SimpleSection.card_dvd_of_solvable_representation hS π hπ k
  rw [card_identity_su3_four (LineCore.Parabolic.middleForm J) hcard hconj rfl,
    nat_card_alternatingGroup,Nat.card_fin] at hdiv
  norm_num at hdiv

private theorem no_six_plane
    {A : Type*} [Group A] [Group.IsPerfect A]
    (hS : ¬ Group.IsSolvable (alternatingGroup (Fin 6)))
    (π : A →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (r : A →* planeParabolic J) [Group.IsSolvable r.ker] : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨c,hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let : Group.IsPerfect r.range := Group.IsPerfect.range r
  have hr : r.range ≤ PlaneCore.planeRadicalLevi J c hc hJ := by
    rw [← PlaneCore.plane_solvableResidual_eq J hcard hconj c hc hJ]
    exact le_solvableResidual_of_isPerfect r.range
  let j := r.codRestrict _ (fun x => hr ⟨x,rfl⟩)
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun _ hx => congrArg Subtype.val hx))
    (inclusion_injective _)
  let q := PlaneCore.planeRadicalLeviProjection J c hc hJ
  have hq : IsPGroup 2 q.ker := by
    rw [PlaneCore.planeRadicalLeviProjection_ker]
    exact (PlaneCore.projectiveUnipotent_isPGroup J hJ).comap_subtype
  let : Group.IsNilpotent q.ker := hq.isNilpotent
  let k := q.comp j
  let : Group.IsSolvable k.ker := by
    change Group.IsSolvable (q.comp j).ker
    rw [← MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker j q.ker
  exact no_rankOne_quotient_in_binary_linear_two hS six_not_two_exponent π hπ k

/-- No perfect residual with an actual alternating-six quotient and soluble
representation kernel normalizes a nonidentity two-subgroup of PSU₅(4). -/
theorem no_six_unitary_five_local
    {A : Type*} [Group A] [Group.IsPerfect A]
    (π : A →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.IsPerfect.ofSurjective hπ
  have hS := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨W,hn,hi,_,hNW⟩ := IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
    J hJ (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  obtain ⟨b,g,hg⟩ := IsotropicTransitivity.transitive J hcard hconj hJ W hn hi
  have he : parabolic J W = (if b then planeParabolic J else lineParabolic J).map
      (MulAut.conj (project J g)).toMonoidHom := by
    rw [hg,IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hNW
  let j := (MulAut.conj (project J g)⁻¹).toMonoidHom.comp r
  have hj : j.range ≤ (if b then planeParabolic J else lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hNW (hr ⟨x,rfl⟩)
    change (project J g)⁻¹ * r x * ((project J g)⁻¹)⁻¹ ∈ _
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj (project J g)⁻¹).injective (he.trans (map_one _).symm)))
    (inclusion_injective _)
  cases b
  · exact no_six_line hS π hπ J hcard hconj hJ k
  · exact no_six_plane hS π hπ J hcard hconj hJ k

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
