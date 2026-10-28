module

public import Theory.LinearAlgebra.MatrixTwoCentralizer
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralDomain

/-!
# Odd-prime subgroups of SL₂ over prime fields

Every finite odd p-group admitting a faithful representation in SL₂ over a
prime field is cyclic. In the defining characteristic, Sylow conjugacy embeds
it in the additive prime field. In a different characteristic, a nonidentity
central element is nonscalar. Its eigenline over an algebraic closure is
preserved by the whole group, because its matrix centralizer consists of
linear combinations of it and the identity. The eigenline character is
faithful: a determinant-one matrix fixing a vector is unipotent of order
dividing the field characteristic, which is coprime to p.

The eigenline construction extends the characteristic-two proof in
`Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear`.
This supplies the SL₂ step of Aschbacher–Smith, *The Classification of
Quasithin Groups*, A.1.32, printed p.28.
-/

open Matrix

namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] {r : ℕ} [Fact r.Prime] [CharP F r]
private theorem char_pow_eq_one_of_fixed_vector (A : SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) (hv : v ≠ 0) (hfix : A.val *ᵥ v = v) : A ^ r = 1 := by
  have hd : det (A.val - 1) = 0 := exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by simpa only [sub_mulVec, one_mulVec, sub_eq_zero] using hfix⟩
  have ha := A.property
  have ht : A.val 0 0 + A.val 1 1 = 2 := by
    simp only [det_fin_two, sub_apply, one_apply, Fin.isValue, ite_true,
      zero_ne_one, one_ne_zero, ite_false, sub_zero] at hd
    simp only [det_fin_two] at ha
    linear_combination ha - hd
  simp only [det_fin_two] at ha
  have hn : (A.val - 1) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination A.val 0 0 * ht - ha
    · linear_combination A.val 0 1 * ht
    · linear_combination A.val 1 0 * ht
    · linear_combination A.val 1 1 * ht - ha
  let : CharP (Matrix (Fin 2) (Fin 2) F) r := {
    cast_eq_zero_iff k := by
      simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
        CharP.cast_eq_zero_iff F r k, forall_const]
  }
  have hnr : (A.val - 1) ^ r = 0 := pow_eq_zero_of_le (Fact.out : r.Prime).two_le hn
  apply Subtype.ext
  change A.val ^ r = 1
  calc
    A.val ^ r = ((A.val - 1) + 1) ^ r := by rw [sub_add_cancel]
    _ = (A.val - 1) ^ r + 1 ^ r := add_pow_char_of_commute r (Commute.one_right _)
    _ = 1 := by rw [hnr, one_pow, zero_add]

private theorem cyclic_of_injective_of_algClosed [IsAlgClosed F]
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2) (hpr : p ≠ r)
    (ρ : P →* SpecialLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    IsCyclic P := by
  classical
  rcases subsingleton_or_nontrivial P with hPsub | hPnontriv
  · let := hPsub
    infer_instance
  let := hPnontriv
  let := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  let A := ρ (z : P)
  have hA : ¬ ∃ a : F, A.val = a • 1 := by
    rintro ⟨a, ha⟩
    have hdet := A.property
    rw [ha, det_smul, det_one, Fintype.card_fin, mul_one] at hdet
    have hA2 : A ^ 2 = 1 := by
      apply Subtype.ext
      change A.val ^ 2 = 1
      rw [ha, smul_pow, hdet, one_pow, one_smul]
    have hz2 : (z : P) ^ 2 = 1 := hρ (by simpa only [map_pow, map_one] using hA2)
    have hz1 : (z : P) = 1 :=
      (hP.powEquiv (hp.out.odd_of_ne_two hp2).coprime_two_right).injective
        (by simpa only [IsPGroup.powEquiv_apply, one_pow] using hz2)
    exact hz (Subtype.ext hz1)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A.val)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A.val *ᵥ v = μ • v := hv.apply_eq_smul
  have hχ : ∀ x : P, ∃ c : F, (ρ x).val *ᵥ v = c • v := by
    intro x
    have hcomm : A.val * (ρ x).val = (ρ x).val * A.val := by
      have hzcomm := (Subgroup.mem_center_iff.mp z.property x).symm
      have heq : A * ρ x = ρ x * A := by
        simpa only [map_mul] using congrArg ρ hzcomm
      exact congrArg (fun g : SpecialLinearGroup (Fin 2) F => g.val) heq
    obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul_of_commute_two
      A.val (ρ x).val hA hcomm
    refine ⟨a + b * μ, ?_⟩
    rw [hab, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hAv,
      smul_smul, add_smul]
  let χ : P → F := fun x => (hχ x).choose
  have hχspec (x : P) : (ρ x).val *ᵥ v = χ x • v := (hχ x).choose_spec
  let f : P →* F := {
    toFun := χ
    map_one' := by
      apply smul_left_injective F hv.2
      change χ 1 • v = (1 : F) • v
      rw [← hχspec]
      simp
    map_mul' := by
      intro x y
      apply smul_left_injective F hv.2
      change χ (x * y) • v = (χ x * χ y) • v
      rw [← hχspec, map_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
        hχspec, mulVec_smul, hχspec, smul_smul, mul_comm]
  }
  apply isCyclic_of_injective_ringHom f
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  have hfix : (ρ x).val *ᵥ v = v := by
    rw [hχspec, show χ x = 1 from hx, one_smul]
  have hxr : x ^ r = 1 := hρ (by
    simpa only [map_pow, map_one] using char_pow_eq_one_of_fixed_vector (ρ x) v hv.2 hfix)
  exact (hP.powEquiv ((hp.out.coprime_iff_not_dvd).mpr
    (fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp.out Fact.out).mp h)))).injective
      (by simpa only [IsPGroup.powEquiv_apply, one_pow] using hxr)

/-- Finite odd p-groups admitting a faithful degree-two determinant-one
representation in a different prime characteristic are cyclic. -/
public theorem isCyclic_of_odd_pGroup_injective_of_ne_char
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2) (hpr : p ≠ r)
    (ρ : P →* SpecialLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    IsCyclic P := by
  let ι := SpecialLinearGroup.map (n := Fin 2) (algebraMap F (AlgebraicClosure F))
  apply cyclic_of_injective_of_algClosed hP hp2 hpr (ι.comp ρ)
  intro x y hxy
  apply hρ
  apply Subtype.ext
  ext i j
  apply (algebraMap F (AlgebraicClosure F)).injective
  exact congrArg (fun g : SpecialLinearGroup (Fin 2) (AlgebraicClosure F) => g.val i j) hxy

/-- Every finite odd p-group embedding in SL₂ over a prime field is cyclic,
including when p is the defining prime. -/
public theorem isCyclic_of_odd_pGroup_injective_primeField
    {P : Type*} [Group P] [Finite P] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2)
    (ρ : P →* SpecialLinearGroup (Fin 2) (ZMod r)) (hρ : Function.Injective ρ) :
    IsCyclic P := by
  by_cases hpr : p = r
  · subst r
    have hI : IsPGroup p ρ.range := hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    obtain ⟨S, hS⟩ := hI.exists_le_sylow
    have hc : IsCyclic S :=
      (sylowEquivAdditive (ZMod p) p S).isCyclic.mp inferInstance
    let := hc
    let : IsCyclic ρ.range := isCyclic_of_injective (Subgroup.inclusion hS)
      (Subgroup.inclusion_injective hS)
    exact isCyclic_of_injective ρ.rangeRestrict (fun a b h => hρ (congrArg Subtype.val h))
  · exact isCyclic_of_odd_pGroup_injective_of_ne_char hP hp2 hpr ρ hρ

end Matrix.SpecialLinearGroup
