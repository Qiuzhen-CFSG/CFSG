module

public import ABG.ChapterII.Section2.UnitaryCard
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.LinearAlgebra.Hermitian.UnitaryCoefficientEquivalence
public import Theory.SpecificGroups.SL2.ThreeCharacteristicTwo
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Characteristic two of the involution centralizers in SU₃(3)

An involution centralizer is the full GU₂(3), by the determinant-corrected
block embedding and the proved special-unitary conjugacy theorem. Entrywise
field transport identifies this GU₂ with ABG's concrete Galois-field model.
Its determinant kernel is actually isomorphic to SL₂(3), whose two-core is
self-centralizing, and the quotient has order four. The normal-extension
criterion therefore gives characteristic two of GU₂(3).

These are comparisons of the concrete groups; the order calculations only
establish the two-group quotient. No recognition by order or two-local
classification is assumed. The argument includes characteristic three and
does not require the semidihedral Sylow construction.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 (repeated as
Theorem 0.1.1(4), printed p.482), and Lemma A.3.21(a), printed p.55;
ABG II.2 Lemma 1, article p.17, for the unitary determinant models.
-/

open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace CFSG.Quasithin.MainConverse.UnitaryThree

private theorem gu_twoCore :
    centralizer (pCore 2 (ABG.GU2 3 1 (by decide)) : Set (ABG.GU2 3 1 (by decide))) ≤
      pCore 2 (ABG.GU2 3 1 (by decide)) := by
  let D := ABG.SU2Level 3 1 (by decide) 0
  have hD : Nat.card D = 24 := by
    exact ABG.SU2Level_card 3 1 (by decide) (by decide) 0 (by decide)
  have hG : Nat.card (ABG.GU2 3 1 (by decide)) = 96 := by
    exact ABG.GU2_card 3 1 (by decide) (by decide)
  have hidx : D.index = 4 := by
    have hh := D.card_mul_index
    rw [hD, hG] at hh
    omega
  let := Fintype.ofFinite (GaloisField 3 1)
  let eF := ZMod.ringEquivOfPrime (GaloisField 3 1) Nat.prime_three
    (by simpa only [← Nat.card_eq_fintype_card, pow_one] using GaloisField.card 3 1 (by decide))
  let e := ((ABG.SU2LevelZeroEquivSpecial 3 1 (by decide)).trans
    (ABG.specialUnitaryTwo_equiv_sl2 3 1 (by decide) (by decide))).trans
      (GorensteinWalter.sl2RingEquiv eF.symm)
  apply Theory.GroupTheory.centralizer_pCore_le_of_normal_pGroup_quotient_of_inf_centralizer_le D
    (IsPGroup.of_card (p := 2) (n := 2) (by change D.index = 4; exact hidx))
  apply (Theory.GroupTheory.inf_centralizer_pCoreIn_le_iff 2 D).mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
    Matrix.SpecialLinearGroup.three_twoCore_self_centralizing

end CFSG.Quasithin.MainConverse.UnitaryThree

open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace CFSG.Quasithin.MainConverse.UnitaryThree

private theorem unitary_twoCore {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 2 F) (hF : Nat.card F = 9)
    (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ 3) :
    centralizer (pCore 2 J.unitarySubgroup : Set J.unitarySubgroup) ≤
      pCore 2 J.unitarySubgroup := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 3 2)
  let eF : F ≃+* GaloisField 3 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card 3 2 (by decide), hF]
    norm_num)
  let e := HermitianForm.unitaryCoefficientEquivOfIdentity eF J
    (ABG.unitaryForm 2 3 1 (by decide)) hJ rfl (by
      intro x
      change eF (J.conj x) = iterateFrobeniusEquiv (GaloisField 3 2) 3 1 (eF x)
      rw [hc, map_pow]
      simp only [iterateFrobeniusEquiv_def, pow_one])
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr gu_twoCore

private def formTwo {F : Type*} [Field F] (J : HermitianForm 3 F) :
    HermitianForm 2 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

/-- Every involution centralizer in normalized SU₃(3) has a self-centralizing
intrinsic two-core, via its actual GU₂(3) block equivalence. -/
public theorem special_involutionCentralizer_twoCore {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hF : Nat.card F = 3 ^ 2)
    (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ 3)
    (z : J.specialSubgroup) (hz : orderOf z = 2) :
    centralizer (pCore 2 (centralizer ({z} : Set J.specialSubgroup)) :
        Set (centralizer ({z} : Set J.specialSubgroup))) ≤
      pCore 2 (centralizer ({z} : Set J.specialSubgroup)) := by
  let := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e := Matrix.SU3.involutionCentralizerEquiv (p := 3) (by decide) hF
    J (formTwo J) hJ rfl hc hc z hz
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    (unitary_twoCore (formTwo J) hF rfl hc)

end CFSG.Quasithin.MainConverse.UnitaryThree
