module

public import Glauberman.SuzukiCharacterization.NormalizerCharacterAction
public import Glauberman.SuzukiCharacterization.CharacterSelectionCore
public import Glauberman.SuzukiCharacterization.RestrictionDegree
public import Theory.Character.MinimalDegree

/-!
# Degree and restriction sums over normalizer character orbits

The nonprincipal irreducibles of the Sylow subgroup form free normalizer
orbits of equal size. Reindexing the ordinary degree-squared identity gives
their weighted degree mass. Normalizer invariance of ambient restrictions
then makes each irreducible multiplicity constant on its orbit.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.3 and equations (3.6), (3.13), pp. 84–86, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open scoped BigOperators
open Subgroup ModularBlock.PrincipalBlockConstruction ModularBlock.RestrictionColumn
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

namespace NormalizerCharacterOrbitData
variable {P : Sylow 2 G} {s : CommutatorSupportData P}
variable (o : NormalizerCharacterOrbitData P s)

private def allCharactersEquiv :
    Option (NonprincipalCharacter P) ≃
      {χ : ClassFunction P // IsIrreducibleCharacter χ} :=
  Equiv.ofBijective (fun x => match x with
    | none => ⟨1, isIrreducibleCharacter_one⟩
    | some χ => ⟨χ.val, χ.property.1⟩) (by
    constructor
    · intro x y h
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some χ =>
          exact False.elim (χ.property.2 (congrArg Subtype.val h).symm)
      | some χ =>
        cases y with
        | none =>
          exact False.elim (χ.property.2 (congrArg Subtype.val h))
        | some ψ =>
          change (⟨χ.val, χ.property.1⟩ :
            {θ : ClassFunction P // IsIrreducibleCharacter θ}) =
            ⟨ψ.val, ψ.property.1⟩ at h
          have hval : χ.val = ψ.val :=
            congrArg (fun x : {θ : ClassFunction P // IsIrreducibleCharacter θ} => x.val) h
          exact congrArg some (Subtype.ext hval)
    · intro χ
      by_cases h : χ.val = 1
      · exact ⟨none, Subtype.ext h.symm⟩
      · exact ⟨some ⟨χ.val, χ.property, h⟩, rfl⟩)

private theorem character_expand (f : ClassFunction P) (hf : IsCharacter f) (x : P) :
    f x = ∑ χ : {χ : ClassFunction P // IsIrreducibleCharacter χ},
      scalarProduct P f χ.val * χ.val x := by
  classical
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨n, ρ, hρ⟩ := hf
  obtain ⟨ι, hι, χ, m, hχ, hinj, hcover, hm, hexp⟩ :=
    Theory.Character.exists_natural_character_decomposition ρ
  let : Fintype ι := hι
  let e : ι ≃ {θ : ClassFunction P // IsIrreducibleCharacter θ} :=
    Equiv.ofBijective (fun j => ⟨χ j, hχ j⟩) (by
      constructor
      · intro a b he
        exact hinj (congrArg Subtype.val he)
      · intro θ
        obtain ⟨j, hj⟩ := hcover θ.val θ.property
        exact ⟨j, Subtype.ext hj⟩)
  calc
    f x = ∑ j : ι, (m j : ℂ) * χ j x := by simpa [hρ] using hexp x
    _ = ∑ j : ι, scalarProduct P f (χ j) * χ j x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show scalarProduct P f (χ j) = (m j : ℂ) by simpa [hρ] using hm j]
    _ = ∑ θ : {θ : ClassFunction P // IsIrreducibleCharacter θ},
        scalarProduct P f θ.val * θ.val x := by
      exact e.sum_comp (fun θ => scalarProduct P f θ.val * θ.val x)

private theorem degree_smul (j : Fin o.r)
    (a : (normalizer (P : Set G)) ⧸ normalizerSylowCore P) :
    ((a • o.rep j : NonprincipalCharacter P).property.1.degree) = o.degree j := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (normalizerSylowCore P) a
  have he := normalizerCharacter_smul_one P n (o.rep j)
  rw [(n • o.rep j : NonprincipalCharacter P).property.1.degree_eq,
    (o.rep j).property.1.degree_eq] at he
  exact_mod_cast he

/-- The nonprincipal squared degree mass, equation (3.6). -/
public theorem degree_sq_mass :
    (normalizerSylowCore P).index * (∑ j : Fin o.r, o.degree j ^ 2) =
      Nat.card P - 1 := by
  classical
  let A := (normalizer (P : Set G)) ⧸ normalizerSylowCore P
  let e : Fin o.r × A ≃ NonprincipalCharacter P :=
    Equiv.ofBijective (fun p => p.2 • o.rep p.1) o.orbit_bijective
  have hsum : ∑ χ : NonprincipalCharacter P, χ.property.1.degree ^ 2 =
      ∑ p : Fin o.r × A, o.degree p.1 ^ 2 := by
    rw [← e.sum_comp (fun χ => χ.property.1.degree ^ 2)]
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (· ^ 2) (o.degree_smul p.1 p.2)
  have hfull := Theory.Character.sum_irreducibleCharacters_degree_sq (G := P)
  let e₀ := allCharactersEquiv (P := P)
  have hcomp := e₀.sum_comp (fun χ => χ.property.degree ^ 2)
  rw [← hcomp] at hfull
  have hprincipal : (isIrreducibleCharacter_one (G := P)).degree = 1 := by
    have he := (isIrreducibleCharacter_one (G := P)).degree_eq
    simpa using congrArg Complex.re he.symm
  simp only [Fintype.sum_option] at hfull
  change (isIrreducibleCharacter_one (G := P)).degree ^ 2 +
    (∑ χ : NonprincipalCharacter P, χ.property.1.degree ^ 2) = Nat.card P at hfull
  rw [hprincipal, one_pow, hsum, Fintype.sum_prod_type] at hfull
  simp only [Finset.sum_const, nsmul_eq_mul] at hfull
  rw [← Finset.mul_sum] at hfull
  have hcard : Nat.card A = (normalizerSylowCore P).index := by
    exact (Subgroup.index_eq_card (normalizerSylowCore P)).symm
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at hfull
  change 1 + (normalizerSylowCore P).index *
    (∑ j : Fin o.r, o.degree j ^ 2) = Nat.card P at hfull
  omega

/-- Real form of the nonprincipal degree mass used in the restriction bound. -/
public theorem degree_sq_mass_real :
    (Nat.card P : ℝ) - 1 =
      (normalizerSylowCore P).index * ∑ j : Fin o.r, (o.degree j : ℝ) ^ 2 := by
  have h := o.degree_sq_mass
  have h' := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_sub Nat.card_pos,
    Nat.cast_one] using h'.symm

private theorem restriction_fixed (d : PrincipalCongruenceBlockData G)
    (i : d.I) (n : normalizer (P : Set G)) (x : P) :
    restriction d P i ((P : Subgroup G).normalizerMonoidHom n x) =
      restriction d P i x := by
  have hf := ofConjClassFunction_isClassFunction (d.chi i)
  have he := hf (x : G) (n : G)
  change d.chi i (ConjClasses.mk ((n : G) * (x : G) * (n : G)⁻¹)) =
    d.chi i (ConjClasses.mk (x : G)) at he
  exact he

private theorem restriction_scalarProduct_smul (d : PrincipalCongruenceBlockData G)
    (i : d.I) (j : Fin o.r) (n : normalizer (P : Set G)) :
    scalarProduct P (restriction d P i) (n • o.rep j).val =
      scalarProduct P (restriction d P i) (o.psi j) := by
  let e := (P : Subgroup G).normalizerMonoidHom n⁻¹
  have h := scalarProduct_comp_mulEquiv e
    (restriction d P i) (o.psi j)
  have hf : (fun x : P => restriction d P i (e x)) = restriction d P i := by
    funext x
    exact restriction_fixed d i n⁻¹ x
  calc
    scalarProduct P (restriction d P i) (n • o.rep j).val =
        scalarProduct P (fun x => restriction d P i (e x))
          (fun x => o.psi j (e x)) := by
      congr 1
      · exact hf.symm
    _ = _ := h

/-- Actual restriction multiplicities and the orbit-weighted degree formula. -/
public theorem exists_restriction_orbit_multiplicities
    (d : PrincipalCongruenceBlockData G)
    (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (restriction d P i) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (restriction d P i) s.theta = c₁ i) :
    ∃ c : d.I → Fin o.r → ℕ,
      (∀ i j, scalarProduct P (restriction d P i) (o.psi j) = c i j) ∧
      (∀ i, c i o.firstIndex = c₁ i) ∧
      (∀ i, (d.chi i (ConjClasses.mk 1)).re = (c₀ i : ℝ) +
        (normalizerSylowCore P).index *
          ∑ j : Fin o.r, (c i j : ℝ) * o.degree j) := by
  classical
  let : Fintype P := Fintype.ofFinite P
  have hψ (j : Fin o.r) : IsCharacter (o.psi j) := by
    obtain ⟨n, ρ, _, hρ⟩ := o.psi_irreducible j
    exact ⟨n, ρ, hρ⟩
  choose c hc using fun i j =>
    (restriction_isCharacter d P i).scalarProduct_eq_nat (hψ j)
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    have he : (c i o.firstIndex : ℂ) = (c₁ i : ℂ) := by
      rw [← hc i o.firstIndex, o.psi_first, hc₁ i]
    exact_mod_cast he
  · intro i
    let A := (normalizer (P : Set G)) ⧸ normalizerSylowCore P
    let e : Fin o.r × A ≃ NonprincipalCharacter P :=
      Equiv.ofBijective (fun p => p.2 • o.rep p.1) o.orbit_bijective
    let e₀ := allCharactersEquiv (P := P)
    have hex := character_expand (P := P) (restriction d P i)
      (restriction_isCharacter d P i) 1
    change d.chi i (ConjClasses.mk 1) = _ at hex
    have hcomp := e₀.sum_comp (fun χ =>
      scalarProduct P (restriction d P i) χ.val * χ.val 1)
    rw [← hcomp] at hex
    simp only [Fintype.sum_option] at hex
    change d.chi i (ConjClasses.mk 1) =
      scalarProduct P (restriction d P i) 1 * 1 +
        ∑ χ : NonprincipalCharacter P,
          scalarProduct P (restriction d P i) χ.val * χ.val 1 at hex
    rw [hc₀ i, mul_one, ← e.sum_comp (fun χ =>
      scalarProduct P (restriction d P i) χ.val * χ.val 1)] at hex
    simp only [Fintype.sum_prod_type] at hex
    have horbit (j : Fin o.r) (a : A) :
        scalarProduct P (restriction d P i) (a • o.rep j).val = c i j := by
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (normalizerSylowCore P) a
      rw [normalizerQuotient_mk_smul, o.restriction_scalarProduct_smul d i j n]
      exact hc i j
    change d.chi i (ConjClasses.mk 1) =
      (c₀ i : ℂ) + ∑ j : Fin o.r, ∑ a : A,
        scalarProduct P (restriction d P i) (a • o.rep j).val *
          (a • o.rep j : NonprincipalCharacter P).val 1 at hex
    simp_rw [horbit] at hex
    have hdegree (j : Fin o.r) (a : A) :
        (a • o.rep j : NonprincipalCharacter P).val 1 = (o.degree j : ℂ) := by
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (normalizerSylowCore P) a
      rw [normalizerQuotient_mk_smul, normalizerCharacter_smul_one]
      exact o.psi_one j
    simp_rw [hdegree] at hex
    simp only [Finset.sum_const, nsmul_eq_mul] at hex
    rw [← Finset.mul_sum] at hex
    have hcard : Nat.card A = (normalizerSylowCore P).index := by
      exact (Subgroup.index_eq_card (normalizerSylowCore P)).symm
    simp only [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at hex
    have hre := congrArg Complex.re hex
    simpa only [Complex.add_re, Complex.natCast_re, Complex.mul_re,
      Complex.natCast_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum,
      Complex.natCast_re, Complex.natCast_im, Nat.cast_sum,
      Nat.cast_mul, Nat.cast_ofNat] using hre

end NormalizerCharacterOrbitData
end Glauberman.SuzukiCharacterization
