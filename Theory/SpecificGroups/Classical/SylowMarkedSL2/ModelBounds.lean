module
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer.Geometry
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import GorensteinWalter.PSL2Cardinality
/-!
# Derived involution centralizers in the five-field classical models

The actual SL₃ involution centralizer is GL₂; the actual SU₃ centralizer is
GU₂ after Hermitian form transport. The determinant kernel in either case is
SL₂(5), so the first derived subgroup has order at most 120. All field and
stored Hermitian-form conventions are retained.
Source: Aschbacher–Smith A.3.21(a), p.55, used in C.5.12, p.163.
-/
public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {F : Type*} [Field F] [Finite F]
theorem linear_derived_centralizer_card_le (hF : Nat.card F = 5)
    (z : SL(3,F)) (hz : orderOf z = 2) :
    Nat.card (commutator (centralizer ({z} : Set SL(3,F)))) ≤ 120 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow (p := 5) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card,pow_one] using hF)
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by decide : 5 ≠ 2)
  let C := centralizer ({z} : Set SL(3,F))
  let e := SL3.involutionCentralizerEquiv F z hz h2
  let f : commutator C →* (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker :=
    (e.toMonoidHom.comp (commutator C).subtype).codRestrict _ (fun x =>
      Abelianization.commutator_subset_ker (GeneralLinearGroup.det.comp e.toMonoidHom) x.property)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val h
  have he := Nat.card_le_card_of_injective f hf
  rw [← Nat.card_congr (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).toEquiv,
    GorensteinWalter.sl2_card_formula,hF] at he
  norm_num at he
  exact he

theorem unitary_derived_centralizer_card_le (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) (hc : ∀ x, J.conj x = x ^ 5)
    (z : J.specialSubgroup) (hz : orderOf z = 2) :
    Nat.card (commutator (centralizer ({z} : Set J.specialSubgroup))) ≤ 120 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let E := GaloisField 5 (2 * 1)
  let J3 := ABG.unitaryForm 3 5 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 5 1 one_ne_zero
  have hE : Nat.card E = 5 ^ 2 := by
    change Nat.card (GaloisField 5 (2*1)) = 5^2
    rw [GaloisField.card 5 (2*1) (by decide)]
  have hJ : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1
      (by decide) (by simpa using hF) (by simpa only [pow_one] using hc)
  have hJ3 : Nat.card {x : E // J3.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J3.conj 5 1
      (by decide) (by simpa only [pow_one] using hE) (by intro x; exact iterateFrobeniusEquiv_def _ _ _ _)
  obtain ⟨s⟩ := J.nonempty_specialEquiv_of_card J3 5 (by simpa using hF) hJ hE hJ3
  have h2 : (2 : E) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime E Nat.prime_two (by decide : 5 ≠ 2)
  let C := centralizer ({z} : Set J.specialSubgroup)
  let eC := (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv s z).trans
    (Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer.involutionCentralizerEquiv
      J3 J2 rfl rfl rfl 5 hE hJ3 h2 (s z) ((s.orderOf_eq z).trans hz)).symm
  let e2 := (ABG.specialUnitaryTwo_equiv_sl2 5 1 (by decide) (by decide)).trans
    (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP 5).toRingEquiv)
  let f : commutator C →* J2.unitaryDet.ker :=
    (eC.toMonoidHom.comp (commutator C).subtype).codRestrict _ (fun x =>
      Abelianization.commutator_subset_ker (J2.unitaryDet.comp eC.toMonoidHom) x.property)
  let j := e2.toMonoidHom.comp (J2.unitaryDetKernelEquiv.toMonoidHom.comp f)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply eC.injective
    exact congrArg Subtype.val (J2.unitaryDetKernelEquiv.injective (e2.injective h))
  have he := Nat.card_le_card_of_injective j hj
  rw [GorensteinWalter.sl2_card_formula,Nat.card_zmod] at he
  norm_num at he
  exact he
end Theory.SpecificGroups.Classical.SylowMarkedSL2
