module
public import Theory.SpecificGroups.PSL3.SmallPrimeSylowCentralizers
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel

/-!
# Two-group radicals of PSL3(5) Sylow-fixer centralizers

The literal involution centralizer is GL2(5): the SL3 scalar center is
trivial and the involution eigenspace decomposition supplies the block
isomorphism. The determinant kernel is quasisimple SL2(5), with two-group
center and determinant quotient of order four, so GL2(5) has two-group
solvable radical. Every pointwise Sylow-two fixer is inner.

Source: GLS3 2.5.12(a), the standard involution eigenspace calculation,
and Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.SmallPrimeSylowCentralizers
variable {F : Type*} [Field F] [Finite F]

private theorem gl2_radical_two (hF : Nat.card F = 5) :
    IsPGroup 2 (solvableRadical (GL (Fin 2) F)) := by
  let D := (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker
  let e := SpecialLinearGroup.determinantKernelEquiv (Fin 2) F
  let : IsQuasisimple D := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    (by rw [hF]; decide) e.symm
  have hz : IsPGroup 2 (center D) :=
    ((GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F (by rw [hF]; decide)).of_equiv
      (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker F))).of_equiv (centerCongr e)
  have hu : IsPGroup 2 Fˣ := IsPGroup.of_card (n := 2) (by rw [Nat.card_units,hF]; decide)
  have hq : IsPGroup 2 (GL (Fin 2) F ⧸ D) :=
    (hu.to_subgroup _).of_equiv (QuotientGroup.quotientKerEquivRange
      (GeneralLinearGroup.det (n := Fin 2) (R := F))).symm
  exact radical_isTwoGroup_of_quasisimple_two_quotient D hz hq

/-- The full fixed subgroup of a Sylow-fixing involution of PSL3(5)
has two-group solvable radical, with the actual coefficient field retained. -/
theorem quintic_sylow_fixer_radical_two
    [IsSimpleGroup PSL(3,F)] [Group.IsPerfect PSL(3,F)] (hF : Nat.card F = 5)
    (P : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) : IsPGroup 2 (solvableRadical a.fixedSubgroup) := by
  obtain ⟨t,rfl⟩ := sylow_fixer_inner (Or.inr hF) P a ha hP
  have hz : center PSL(3,F) = ⊥ := center_eq_bot_of_simple_perfect
  have ht : orderOf t = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz) t).symm.trans ha
  have hZ : center SL(3,F) = ⊥ := (SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [hF]; decide)
  let e := SL3.equivProjectiveOfCenterEqBot F hZ
  let x := e.symm t
  have hx : orderOf x = 2 := (e.symm.orderOf_eq t).trans ht
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide)
  let eC := (CentralizerSmallKernelTransport.centralizerEquiv e x).symm.trans
    (SL3.involutionCentralizerEquiv F x hx h2)
  have he : e x = t := e.apply_symm_apply t
  rw [MulAut.fixedSubgroup_conj]
  let j := (MulEquiv.subgroupCongr (congrArg (fun y : PSL(3,F) => centralizer ({y} : Set PSL(3,F))) he.symm)).trans eC
  let jR := (j.subgroupMap (solvableRadical (centralizer ({t} : Set PSL(3,F))))).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv j))
  exact (gl2_radical_two hF).of_equiv jR.symm
end Matrix.PSL3.SmallPrimeSylowCentralizers
