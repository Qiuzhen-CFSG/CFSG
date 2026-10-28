module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.PointRestriction.SimpleDegrees

/-!
# Binary simple degrees through thirty for PSL(3,4)

Inflate through the actual central quotient SL(3,4) → PSL(3,4), then extend
its commuting endomorphism field to an algebraic closure. The proved tensor-word
catalogue and exact Frobenius period leave binary degrees 1, 6, 9, 16 and 18
in the required window. The existing projective theorem excludes degree six.

A binary degree-eighteen module would have Schur degree two and one of the
mixed natural–dual words. A nonidentity central scalar has character c or c²
on these words. Inflation kills that scalar, forcing character one instead.
This excludes eighteen, leaving precisely the possible degrees 1, 9 and 16.
Absolute irreducibility over the binary field is never assumed.

The dimension and Frobenius-period calculation follows GLS III §§2.8.6,
2.8.8 and 2.8.10(c), using the repository's proved SL₃ catalogue. It extends
PointRestriction.SimpleDegrees and adapts the finite-word argument in
M22James/Uniqueness/PointRestriction/LocalCatalogue/SmallConstituents.lean.
The consumer is the M22 degree-gap reduction for Guralnick–Malle I,
Proposition 5.1, pp.15–16, and Aschbacher–Smith K, printed pp.451–452 and 457.
-/

open Representation
open scoped MatrixGroups TensorProduct MonoidAlgebra
open Representation.SL3.BinaryDefiningFactors

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.PointSimpleDegrees

private lemma small_word_degrees (w : List Factor) (hlen : w.length = 2)
    (s d : ℕ) (hd : d = s * wordDegree w) (hle : d ≤ 30)
    (hperiod : ∀ j, w.rotate j = w ↔ s ∣ j) :
    d = 1 ∨ d = 6 ∨ d = 9 ∨ d = 16 ∨ d = 18 := by
  have hs : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp
    ((hperiod 2).mp (hlen ▸ List.rotate_length w))
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hs with rfl | rfl
  · have hr := (hperiod 1).mpr (one_dvd 1)
    have hab : a = b := (by simpa using hr : b = a ∧ a = b).2
    subst b
    cases a <;> simp [wordDegree, Factor.dimension] at hd <;> omega
  · have hr := (hperiod 1).not.mpr (by decide : ¬ 2 ∣ 1)
    cases a <;> cases b <;>
      simp_all [wordDegree, Factor.dimension]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) Matrix.PSL3Four.SL W) [σ.IsIrreducible]

private abbrev SchurField := Module.End (ZMod 2)[Matrix.PSL3Four.SL] σ.asModule
private abbrev SplittingField := AlgebraicClosure (SchurField σ)
private instance schurField_charTwo : CharP (SchurField σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField σ)).injective 2

include σ in
private theorem sl_simple_degree (hhi : Module.finrank (ZMod 2) W ≤ 30) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 6 ∨
    Module.finrank (ZMod 2) W = 9 ∨ Module.finrank (ZMod 2) W = 16 ∨
    Module.finrank (ZMod 2) W = 18 := by
  let : Algebra (ZMod 2) Matrix.PSL3Four.F := ZMod.algebra _ 2
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra _ 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars (SplittingField σ) σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SplittingField σ)
  let ι : Matrix.PSL3Four.F →+* SplittingField σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := Matrix.PSL3Four.F)
      (M := SplittingField σ)).toRingHom
  have hcard : Nat.card Matrix.PSL3Four.F = 2 ^ 2 := by
    simpa using Matrix.PSL3Four.card_F
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField σ) σ.endFieldRep)
  have hp := word_rotate_iff_schurDegree_dvd σ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h =>
      (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h) ⟨e⟩
  have hdim : Module.finrank (ZMod 2) W =
      Representation.schurDegree 2 σ * wordDegree w := by
    rw [Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  exact small_word_degrees w hw _ _ hdim hhi hp

private theorem simple_degree_candidates
    (τ : Representation (ZMod 2) Matrix.PSL3Four.PSL W) [τ.IsIrreducible]
    (hhi : Module.finrank (ZMod 2) W ≤ 30) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 9 ∨
    Module.finrank (ZMod 2) W = 16 ∨ Module.finrank (ZMod 2) W = 18 := by
  let π := QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)
  let σ : Representation (ZMod 2) Matrix.PSL3Four.SL W := τ.comp π
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff π (QuotientGroup.mk'_surjective _) τ).mpr inferInstance
  have h := sl_simple_degree σ hhi
  by_cases hsmall : Module.finrank (ZMod 2) W ≤ 12
  · rcases PointRestriction.SimpleDegrees.simple_degree τ hsmall with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · omega



private lemma word_of_degree_eighteen (w : List Factor) (hlen : w.length = 2)
    (s : ℕ) (hd : 18 = s * wordDegree w)
    (hperiod : ∀ j, w.rotate j = w ↔ s ∣ j) :
    w = [.natural, .dual] ∨ w = [.dual, .natural] := by
  have hs : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp
    ((hperiod 2).mp (hlen ▸ List.rotate_length w))
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hs with rfl | rfl
  · cases a <;> cases b <;> simp_all [wordDegree, Factor.dimension]
  · have hr := (hperiod 1).not.mpr (by decide : ¬ 2 ∣ 1)
    cases a <;> cases b <;> simp_all [wordDegree, Factor.dimension]


open Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation

private def scalarElement (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1) :
    Matrix.PSL3Four.SL := ⟨c • 1, by simp [hc]⟩

private lemma scalarElement_inv (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1) :
    (scalarElement c hc)⁻¹ = scalarElement (c ^ 2) (by rw [← pow_mul, Nat.mul_comm 2 3,
      pow_mul, hc, one_pow]) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (c • (1 : Matrix (Fin 3) (Fin 3) Matrix.PSL3Four.F)) *
    (c ^ 2 • 1) = 1
  simp only [Matrix.mul_smul, mul_one, smul_smul]
  rw [← pow_succ, hc, one_smul]

private lemma scalar_trace (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1) :
    Matrix.trace (scalarElement c hc).val = c := by
  have h3 : (3 : Matrix.PSL3Four.F) = 1 := by
    have h := CharTwo.add_self_eq_zero (1 : Matrix.PSL3Four.F)
    linear_combination h
  simp [scalarElement, h3]

private theorem mixed_character_ne_one {K : Type*} [Field K] [CharP K 2]
    (ι : Matrix.PSL3Four.F →+* K) (c : Matrix.PSL3Four.F)
    (hc : c ^ 3 = 1) (hc1 : c ≠ 1) :
    (wordRep ι [.natural, .dual]).character (scalarElement c hc) ≠ 1 ∧
    (wordRep ι [.dual, .natural]).character (scalarElement c hc) ≠ 1 := by
  have htrace := scalar_trace c hc
  have hitrace : Matrix.trace (scalarElement c hc)⁻¹.val = c ^ 2 := by
    rw [scalarElement_inv, scalar_trace]
  have hc2 : c ^ 2 ≠ 1 := by
    intro h
    apply hc1
    have hh := Matrix.PSL3Four.pow_four c
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow] at hh
    exact hh.symm
  constructor
  · rw [wordRep_character_polynomial]
    simp only [wordPolynomial, factorPolynomial, MvPolynomial.eval_mul,
      MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_pow,
      mul_one, htrace, hitrace]
    rw [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, Matrix.PSL3Four.pow_four,
      ← pow_two, ← map_one ι]
    exact fun h => hc2 (ι.injective h)
  · rw [wordRep_character_polynomial]
    simp only [wordPolynomial, factorPolynomial, MvPolynomial.eval_mul,
      MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_pow,
      mul_one, htrace, hitrace]
    rw [← pow_two, ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl,
      Matrix.PSL3Four.pow_four, ← map_one ι]
    exact fun h => hc1 (ι.injective h)

private theorem exists_central_scalar : ∃ c : Matrix.PSL3Four.F,
    c ≠ 1 ∧ c ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := Matrix.PSL3Four.exists_fieldFrobenius_ne
  have hc0 : c ≠ 0 := by intro h; apply hc; simp [h]
  have hc1 : c ≠ 1 := by intro h; apply hc; simp [h]
  refine ⟨c, hc1, ?_⟩
  apply mul_right_cancel₀ hc0
  simpa only [← pow_succ, one_mul] using Matrix.PSL3Four.pow_four c

private theorem scalarElement_central (c : Matrix.PSL3Four.F) (hc : c ^ 3 = 1) :
    scalarElement c hc ∈ Subgroup.center Matrix.PSL3Four.SL := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨c, by simpa using hc, ?_⟩
  ext i j
  simp [scalarElement, Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

private theorem scalar_extension_eq_one
    (σ : Representation (ZMod 2) Matrix.PSL3Four.SL W) [σ.IsIrreducible]
    (g : Matrix.PSL3Four.SL) (h : σ g = 1) :
    extendScalars (SplittingField σ) σ.endFieldRep g = 1 := by
  have he : σ.endFieldRep g = 1 := by
    ext v
    apply σ.asModuleEquiv.injective
    change σ.asModuleEquiv (σ.endFieldRep g v) = σ.asModuleEquiv v
    simp only [endFieldRep_apply, LinearEquiv.apply_symm_apply, h, Module.End.one_apply]
  rw [extendScalars_apply, he, LinearMap.baseChange_one]

private theorem simple_degree_ne_eighteen
    (τ : Representation (ZMod 2) Matrix.PSL3Four.PSL W) [τ.IsIrreducible] :
    Module.finrank (ZMod 2) W ≠ 18 := by
  intro hd
  let π := QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)
  let σ : Representation (ZMod 2) Matrix.PSL3Four.SL W := τ.comp π
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff π (QuotientGroup.mk'_surjective _) τ).mpr inferInstance
  let : Algebra (ZMod 2) Matrix.PSL3Four.F := ZMod.algebra _ 2
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra _ 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars (SplittingField σ) σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SplittingField σ)
  let ι : Matrix.PSL3Four.F →+* SplittingField σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := Matrix.PSL3Four.F)
      (M := SplittingField σ)).toRingHom
  have hcard : Nat.card Matrix.PSL3Four.F = 2 ^ 2 := by
    simpa using Matrix.PSL3Four.card_F
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField σ) σ.endFieldRep)
  have hp := word_rotate_iff_schurDegree_dvd σ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h =>
      (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h) ⟨e⟩
  have hdim : 18 = Representation.schurDegree 2 σ * wordDegree w := by
    rw [← hd, Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  obtain ⟨c, hc1, hc⟩ := exists_central_scalar
  let z := scalarElement c hc
  have hz : σ z = 1 := by
    change τ (π z) = 1
    rw [show π z = 1 from
      (QuotientGroup.eq_one_iff z).mpr (scalarElement_central c hc)]
    exact τ.map_one
  have hchar : (wordRep ι w).character z = (wordDegree w : SplittingField σ) := by
    rw [← char_iso e]
    change LinearMap.trace _ _ (extendScalars (SplittingField σ) σ.endFieldRep z) = _
    rw [scalar_extension_eq_one σ z hz, LinearMap.trace_one,
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  have h9 : (9 : SplittingField σ) = 1 := by
    have h2 := CharP.cast_eq_zero (SplittingField σ) 2
    linear_combination 4 * h2
  obtain hn | hn := word_of_degree_eighteen w hw _ hdim hp
  · subst w
    rw [show wordDegree [.natural, .dual] = 9 from rfl, Nat.cast_ofNat, h9] at hchar
    exact (mixed_character_ne_one ι c hc hc1).1 hchar
  · subst w
    rw [show wordDegree [.dual, .natural] = 9 from rfl, Nat.cast_ofNat, h9] at hchar
    exact (mixed_character_ne_one ι c hc hc1).2 hchar

/-- The only binary simple degrees at most thirty for the actual projective
group are one, nine, and sixteen. -/
theorem simple_degree
    (τ : Representation (ZMod 2) Matrix.PSL3Four.PSL W) [τ.IsIrreducible]
    (hhi : Module.finrank (ZMod 2) W ≤ 30) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 9 ∨
      Module.finrank (ZMod 2) W = 16 := by
  have h := simple_degree_candidates τ hhi
  have hn := simple_degree_ne_eighteen τ
  omega


end Representation.MathieuSmall.M22Recognition.DegreeThirty.PointSimpleDegrees
