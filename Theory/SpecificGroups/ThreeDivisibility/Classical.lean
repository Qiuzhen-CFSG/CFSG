module

public import Theory.SpecificGroups.ProjectiveLinearThree
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Mathlib.Tactic
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Three-divisibility for small classical and G₂ groups

A companion matrix supplies an order-three projective linear element. For a
three-dimensional Hermitian form, transport to an orthonormal basis and use
its cyclic permutation matrix. A faithful SL₂ subgroup handles G₂; a
commutator of two binary transvections handles its derived binary endpoint.
The symplectic order and the proved binary derived-group equivalence give
three-divisibility for the remaining symplectic carriers.

These are intrinsic statements about the actual matrix groups. No simplicity,
classification or order certificate is assumed. The unitary parameter denotes
the fixed-field order, while the matrix field has its square cardinality.

Source application: Aschbacher--Smith, `refs/quasithin.pdf`, 1.1.5(3),
pp.501--503, and the final implication in 15.3.34, p.1134.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups commutatorElement
namespace Theory.SpecificGroups.ThreeDivisibility


theorem g2 (F : Type*) [Field F] : 3 ∣ Nat.card (Atlas.G2.Model F) := by
  have h : 3 ∣ Nat.card SL(2,F) :=
    (ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)).trans
      (center SL(2,F)).card_quotient_dvd_card
  rw [← Nat.card_congr (Atlas.G2.PairStabilizer.fixingPairEquivSL2 (F := F)).toEquiv] at h
  exact h.trans (Atlas.G2.PairStabilizer.fixingPair.card_subgroup_dvd_card)

theorem g2_derived : 3 ∣ Nat.card (commutator (Atlas.G2.Model (ZMod 2))) := by
  let a : SL(2,ZMod 2) := ⟨!![1,1;0,1], by decide⟩
  let b : SL(2,ZMod 2) := ⟨!![1,0;1,1], by decide⟩
  have hc : ⁅a,b⁆ ^ 3 = 1 := by decide +kernel
  have hn : ⁅a,b⁆ ≠ 1 := by decide +kernel
  let e := (Atlas.G2.PairStabilizer.fixingPairEquivSL2 (F := ZMod 2)).symm
  let f := Atlas.G2.PairStabilizer.fixingPair.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let c : commutator (Atlas.G2.Model (ZMod 2)) := ⟨f ⁅a,b⁆, by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)⟩
  have ho : orderOf c = 3 := orderOf_eq_prime (by
    apply Subtype.ext
    change (f ⁅a,b⁆) ^ 3 = 1
    rw [← map_pow, hc, map_one]) (by
    intro he
    apply hn
    exact hf ((congrArg Subtype.val he).trans (map_one f).symm))
  simpa only [ho] using _root_.orderOf_dvd_natCard c

theorem symplectic (F : Type*) [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2^f) :
    3 ∣ Nat.card (Matrix.symplecticGroup (Fin 2) F ⧸
      center (Matrix.symplecticGroup (Fin 2) F)) := by
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  rw [← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv,
    Theory.SpecificGroups.SymplecticFour.card_sp, hF]
  have he : ((2^f)^2)%3 = 1 := by
    rw [← pow_mul, Nat.mul_comm f 2, pow_mul, Nat.pow_mod]
    norm_num
  have hd : 3 ∣ (2^f)^2-1 := Nat.dvd_of_mod_eq_zero (by omega)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

theorem symplectic_derived :
    3 ∣ Nat.card (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2) ⧸
      center (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) := by
  rw [Nat.card_congr Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.toEquiv,
    Nat.card_eq_fintype_card, _root_.card_alternatingGroup]
  norm_num

variable {F : Type*} [Field F]
private def cycleLift : SL(3,F) :=
  ⟨!![0,0,1;1,0,0;0,1,0], by simp [Matrix.det_fin_three]⟩
private theorem cycleLift_cube : (cycleLift (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (cycleLift (F := F)).val ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleLift, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
private theorem cycleLift_noncentral : cycleLift (F := F) ∉ center SL(3,F) := by
  intro h
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp h
  have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 0) hr
  simp [cycleLift] at hh

private theorem identity_exists_three (J : HermitianForm 3 F) (hJ : J.form = 1) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J, orderOf x = 3 := by
  let A := SpecialLinearGroup.toGL (cycleLift (F := F))
  have hA : A ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · rw [hJ, mul_one]
      change J.conjTranspose (cycleLift (F := F)).val * (cycleLift (F := F)).val = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cycleLift, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
    · apply Units.ext
      exact (cycleLift (F := F)).property
  let x : ProjectiveSpecialUnitaryMatrixGroup J := ⟨ProjGenLinGroup.mk A, ⟨A,hA,rfl⟩⟩
  refine ⟨x, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    change (ProjGenLinGroup.mk A) ^ 3 = 1
    rw [← map_pow]
    change ProjGenLinGroup.mk ((SpecialLinearGroup.toGL (cycleLift (F := F))) ^ 3) = 1
    rw [← map_pow, cycleLift_cube, map_one, map_one]
  · intro hx
    have hh := congrArg Subtype.val hx
    change ProjGenLinGroup.mk A = 1 at hh
    exact cycleLift_noncentral ((SpecialLinearGroup.toGL_mem_center_iff _).mp
      (ProjGenLinGroup.mk_eq_one.mp hh))

theorem unitary_three_dvd [Finite F] (J : HermitianForm 3 F) (f : ℕ) (hf : 0 < f)
    (hcard : Nat.card F = (2^f)^2) (hconj : ∀ x, J.conj x = x^(2^f)) :
    3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f hf hcard hconj
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J (2^f) hcard hfixed
  let e := HermitianForm.IdentityGram.projectiveEquiv J C hC
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨x, hx⟩ := identity_exists_three (HermitianForm.IdentityGram.identityGram J) rfl
  simpa only [hx] using _root_.orderOf_dvd_natCard x

end Theory.SpecificGroups.ThreeDivisibility
