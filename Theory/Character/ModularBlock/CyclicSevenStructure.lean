module

public import Theory.Character.ModularBlock.CyclicSevenData
public import Theory.Character.ModularBlock.PrimePowerBlockOrthogonality
public import Theory.Character.ModularBlock.PrimeSelector
public import Theory.Character.IrreducibleDegrees

/-!
# Assembling cyclic seven-block structure

For actual cyclic-block spectral rows, the three period values sum to the
exceptional sign. Weak block orthogonality then gives the signed integer
degree equation. Irreducibility supplies positive natural degrees, while
irrationality of each period excludes every exceptional row from the
globally rational-valued characters.

The projector construction discharges orthogonality once actual spectral rows
have been constructed. Existence from the Sylow hypotheses is assembled by
the consumer; it is not assumed or asserted in this interface.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from the project's corresponding cyclic-thirteen module.
-/

public section

noncomputable section
open scoped BigOperators
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- All row, degree, sign, and rationality outputs for the principal block. -/
structure BlockStructure (d : PrimeCongruenceBlockData 7 G) (P : Sylow 7 G)
    extends SpectralRows d P where
  degree : Fin 2 → ℕ
  degree_pos : ∀ j, 0 < degree j
  degree_value : ∀ j : Fin 2,
    d.chi (rows (j.castAdd 3)).val (ConjClasses.mk 1) = (degree j : ℂ)
  exceptionalDegree_pos : 0 < exceptionalDegree
  degree_equation : ∑ j : Fin 2, sign j * (degree j : ℤ) +
    exceptionalSign * (exceptionalDegree : ℤ) = 0
  rational_row : ∀ i : d.I, i ∈ d.block →
    (∀ g : G, ∃ q : ℚ, d.chi i (ConjClasses.mk g) = (q : ℂ)) →
    ∃ j : Fin 2, (rows (j.castAdd 3)).val = i

private theorem ofConj_irreducible {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

/-- A globally rational-valued row cannot be one of the three period rows. -/
theorem SpectralRows.rational_row {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : SpectralRows d P) (i : d.I) (hi : i ∈ d.block)
    (hrat : ∀ g : G, ∃ q : ℚ, d.chi i (ConjClasses.mk g) = (q : ℂ)) :
    ∃ j : Fin 2, (s.rows (j.castAdd 3)).val = i := by
  obtain ⟨k, hk⟩ := s.rows.surjective ⟨i, hi⟩
  have hki : (s.rows k).val = i := congrArg Subtype.val hk
  induction k using Fin.addCases (m := 2) (n := 3) with
  | left j => exact ⟨j, hki⟩
  | right k =>
    exfalso
    apply SevenPeriods.signed_period_not_rational s.root_primitive s.periods k
      s.exceptionalSign s.exceptionalSign_unit
    obtain ⟨q, hq⟩ := hrat s.generator
    refine ⟨q, ?_⟩
    rw [← s.exceptional_value, hki]
    exact hq

/-- Derive the degree equation and rational-row criterion from the spectral rows
and weak block orthogonality. -/
def SpectralRows.toBlockStructure {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : SpectralRows d P)
    (horth : ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) *
      d.chi i (ConjClasses.mk (s.generator : G)) = 0) : BlockStructure d P := by
  let N : Fin 2 → ℕ := fun j =>
    (ofConj_irreducible (d.complete.1 (s.rows (j.castAdd 3)).val)).degree
  have hN (j : Fin 2) :
      d.chi (s.rows (j.castAdd 3)).val (ConjClasses.mk 1) = (N j : ℂ) :=
    (ofConj_irreducible (d.complete.1 (s.rows (j.castAdd 3)).val)).degree_eq
  have hNpos (j : Fin 2) : 0 < N j :=
    (ofConj_irreducible (d.complete.1 (s.rows (j.castAdd 3)).val)).degree_pos
  have hEpos : 0 < s.exceptionalDegree := by
    let h := ofConj_irreducible (d.complete.1 (s.rows ((0 : Fin 3).natAdd 2)).val)
    have heq : h.degree = s.exceptionalDegree := by
      have := h.degree_eq
      change d.chi _ (ConjClasses.mk 1) = _ at this
      rw [s.exceptional_degree] at this
      exact_mod_cast this.symm
    rw [← heq]
    exact h.degree_pos
  have hs : (∑ j : Fin 5, d.chi (s.rows j).val (ConjClasses.mk 1) *
      d.chi (s.rows j).val (ConjClasses.mk (s.generator : G))) = 0 := by
    rw [s.rows.sum_comp (fun i : {i : d.I // i ∈ d.block} =>
      d.chi i.val (ConjClasses.mk 1) * d.chi i.val (ConjClasses.mk (s.generator : G))),
      Finset.sum_coe_sort d.block (fun i =>
        d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk (s.generator : G)))]
    exact horth
  rw [Fin.sum_univ_add (a := 2) (b := 3)] at hs
  have hn : (∑ j : Fin 2, d.chi (s.rows (j.castAdd 3)).val (ConjClasses.mk 1) *
      d.chi (s.rows (j.castAdd 3)).val (ConjClasses.mk (s.generator : G))) =
      ∑ j : Fin 2, (s.sign j : ℂ) * (N j : ℂ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hN, s.nonexceptional_value j s.generator s.generator_ne_one, mul_comm]
  have he : (∑ k : Fin 3, d.chi (s.rows (k.natAdd 2)).val (ConjClasses.mk 1) *
      d.chi (s.rows (k.natAdd 2)).val (ConjClasses.mk (s.generator : G))) =
      (s.exceptionalSign : ℂ) * (s.exceptionalDegree : ℂ) := by
    simp_rw [s.exceptional_degree, s.exceptional_value, ← mul_assoc]
    rw [← Finset.mul_sum, SevenPeriods.sum_periods s.root_primitive]
    ring
  rw [hn, he] at hs
  refine {
    toSpectralRows := s
    degree := N
    degree_pos := hNpos
    degree_value := hN
    exceptionalDegree_pos := hEpos
    degree_equation := ?_
    rational_row := s.rational_row }
  exact_mod_cast hs

/-- An actual integral principal-block projector discharges the orthogonality
premise in the structure construction. -/
def SpectralRows.toBlockStructureOfProjector
    {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : SpectralRows d P) (hP : Nat.card P = 7)
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    (f : R →+* ℂ) (hp : ¬ IsUnit (7 : R))
    (e : MonoidAlgebra R G) (he : IsIdempotentElem e)
    (hc : e ∈ Set.center (MonoidAlgebra R G))
    (hcoeff : ∀ g : G, f (e.coeff g) = (Nat.card G : ℂ)⁻¹ *
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk g⁻¹)) :
    BlockStructure d P := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hpow : (s.generator : G) ^ (7 ^ 1) = 1 := by
    have hcard : Nat.card ↥P = 7 := hP
    have hg : s.generator ^ 7 = 1 := by
      simpa only [hcard] using (pow_card_eq_one' (x := s.generator))
    have hgG : (s.generator : G) ^ 7 = 1 := by exact_mod_cast hg
    simpa only [pow_one] using hgG
  have hne : (s.generator : G) ≠ 1 := by
    intro h
    exact s.generator_ne_one (Subtype.ext h)
  exact s.toBlockStructure
    (PrimePowerBlockOrthogonality.degree_sum_eq_zero_of_projector d d.principal
      f hp e he hc hcoeff s.generator hne hpow)


/-- The localized block projector supplies the degree equation for any actual
spectral enumeration. The remaining existence input is exactly `SpectralRows`. -/
def SpectralRows.blockStructure
    {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : SpectralRows d P) (hP : Nat.card P = 7) : BlockStructure d P := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply Classical.choice
  obtain ⟨e, he, hc, hcoeff⟩ := PrimeSelector.exists_localizedBlockProjector d d.principal
  exact ⟨s.toBlockStructureOfProjector hP
    (BlockOrthogonality.localizationToComplex d.primeIdeal)
    (PrimeSelector.prime_not_isUnit d) e he hc hcoeff⟩

end ModularBlock.CyclicSeven
