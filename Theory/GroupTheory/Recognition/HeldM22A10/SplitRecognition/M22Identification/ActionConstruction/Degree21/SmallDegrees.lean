module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.System
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Rows
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.ConditionalAssembly

/-!
# Janko's minimum nonprincipal degree and uniqueness at degree twenty-one

The elementary row exhaustion proves degree at least twenty for every
nonprincipal irreducible, including those outside the displayed signed family.
The complete-family system and checked arithmetic exclude degree twenty and
prove uniqueness at degree twenty-one. The resulting character statements
retain the actual special inductions as an input and require no existence
assumption at degree twenty-one or Sylow-three normalizer-order hypothesis.

The final adapter applies both claims to the actual `Degree21Character`
consumer, given the independently constructed character and odd-order spectrum.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
p.16. Construction of the special inductions and the character itself belongs
to the source-theorem assembly, independently of these two assertions.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
open LocalModelDichotomy CharacterOrder OrderExhaustion
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Every small actual irreducible has one of the four explicitly enumerated
rows. No selected signed family restricts the quantifier on the character. -/
public theorem small_irreducible_rows (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1)
    (hn : hχ.degree ≤ 21) :
    (hχ.degree = 20 ∧ (multiplicities I hχ = ![0, 0, -1, 1, -1] ∨
      multiplicities I hχ = ![1, 0, 0, 0, -1])) ∨
    (hχ.degree = 21 ∧ (multiplicities I hχ = ![0, 0, 0, 1, -1] ∨
      multiplicities I hχ = ![1, 0, 1, 0, -1])) := by
  have hu := (SignedAnalysis.unit_multiplicities_and_janko_decomposition D k L I
    (hasSuzukiPairings_of_localAnalysis D k L I)).1
  exact small_rows hχ.degree (multiplicities I hχ) hχ.degree_pos
    (hcard ▸ hχ.degree_dvd_card) hn (multiplicities_unit I hu hχ)
    (E_fixed_nonnegative D k L hχ _ (involutionValue_eq I hχ))
    (involution_lt_degree D hχ hnp _ (involutionValue_eq I hχ))
    (degree_congruence_mod128 D k L I hχ _ (multiplicities_values I hχ))

/-- All degrees below twenty are excluded by the local row calculation,
before using the complete-family arithmetic. -/
public theorem minimum_ge_twenty (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1) :
    (20 : ℝ) ≤ (χ 1).re := by
  have hn : 20 ≤ hχ.degree := by
    by_contra hh
    have hs := small_irreducible_rows D k L hcard I hχ hnp (by omega)
    rcases hs with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  rw [hχ.degree_eq]
  simpa using (show (20 : ℝ) ≤ hχ.degree by exact_mod_cast hn)

/-- Transfer a numerical exclusion and uniqueness theorem to actual
irreducibles. The arithmetic premise is quantified over arbitrary finite
index types, not over group characters. -/
public theorem minimum_and_unique_of_arithmetic (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    (harith : ∀ {J : Type} [Fintype J], ∀ S : DegreeSystem J,
      (∀ j, S.degree j ≠ 20) ∧
      (∀ j l, S.degree j = 21 → S.degree l = 21 → j = l)) :
    (∀ χ : ClassFunction G, IsIrreducibleCharacter χ → χ ≠ 1 →
      (21 : ℝ) ≤ (χ 1).re) ∧
    (∀ χ ψ : ClassFunction G, IsIrreducibleCharacter χ → IsIrreducibleCharacter ψ →
      χ 1 = 21 → ψ 1 = 21 → χ = ψ) := by
  obtain ⟨E⟩ := exists_integralExpansion I
  have hs := harith (degreeSystem L hcard E)
  have hdeg (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ)
      (j : E.Index) (hj : E.character j = χ) : (E.irreducible j).degree = hχ.degree := by
    have he := ((E.irreducible j).degree_eq).symm.trans
      ((congrFun hj 1).trans hχ.degree_eq)
    exact_mod_cast he
  constructor
  · intro χ hχ hnp
    have h20 := minimum_ge_twenty D k L hcard I hχ hnp
    obtain ⟨j, hj⟩ := E.complete χ hχ
    have hj20 : hχ.degree ≠ 20 := by
      simpa only [degreeSystem_degree, hdeg χ hχ j hj] using hs.1 j
    rw [hχ.degree_eq] at h20 ⊢
    simp only [Complex.natCast_re] at h20 ⊢
    have hn : 20 ≤ hχ.degree := by exact_mod_cast h20
    exact_mod_cast (show 21 ≤ hχ.degree by omega)
  · intro χ ψ hχ hψ hc hp
    obtain ⟨j, hj⟩ := E.complete χ hχ
    obtain ⟨l, hl⟩ := E.complete ψ hψ
    have hj21 : (degreeSystem L hcard E).degree j = 21 := by
      rw [degreeSystem_degree, hdeg χ hχ j hj]
      rw [hχ.degree_eq] at hc
      exact_mod_cast hc
    have hl21 : (degreeSystem L hcard E).degree l = 21 := by
      rw [degreeSystem_degree, hdeg ψ hψ l hl]
      rw [hψ.degree_eq] at hp
      exact_mod_cast hp
    exact hj.symm.trans ((congrArg E.character (hs.2 j l hj21 hl21)).trans hl)

/-- Application to the literal degree-21-character consumer. The arithmetic,
character construction, and odd-order spectrum are kept explicit here. -/
public theorem nonempty_of_arithmetic_character_and_odd_structure (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    (harith : ∀ {J : Type} [Fintype J], ∀ S : DegreeSystem J,
      (∀ j, S.degree j ≠ 20) ∧
      (∀ j l, S.degree j = 21 → S.degree l = 21 → j = l))
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) (hloc : HasLocalValues D k χ)
    (hodd : ∀ g : G, Odd (orderOf g) →
      orderOf g ∈ ({1, 3, 5, 7, 11} : Finset ℕ)) :
    Nonempty (Degree21Character G) := by
  obtain ⟨hmin, huniq⟩ := minimum_and_unique_of_arithmetic D k L hcard I harith
  exact nonempty_of_character_and_odd_structure D k L hcard χ hχ hloc hmin
    (fun θ hθ hd => huniq θ χ hθ hχ hd hloc.degree) hodd

/-- Janko's two small-degree assertions for the complete actual irreducible
family, with the finite arithmetic premise discharged. No degree-21 character
is assumed to exist. -/
public theorem minimum_and_unique (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k) :
    (∀ χ : ClassFunction G, IsIrreducibleCharacter χ → χ ≠ 1 →
      (21 : ℝ) ≤ (χ 1).re) ∧
    (∀ χ ψ : ClassFunction G, IsIrreducibleCharacter χ → IsIrreducibleCharacter ψ →
      χ 1 = 21 → ψ 1 = 21 → χ = ψ) :=
  minimum_and_unique_of_arithmetic D k L hcard I
    degreeSystem_excludes_twenty_and_unique_twenty_one

/-- Every actual nonprincipal irreducible has degree at least twenty-one. -/
public theorem minimum_ge_twenty_one (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1) :
    (21 : ℝ) ≤ (χ 1).re :=
  (minimum_and_unique D k L hcard I).1 χ hχ hnp

/-- Any two actual irreducibles of degree twenty-one are the same character. -/
public theorem unique_degree_twenty_one (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hψ : IsIrreducibleCharacter ψ) (hc : χ 1 = 21) (hp : ψ 1 = 21) : χ = ψ :=
  (minimum_and_unique D k L hcard I).2 χ ψ hχ hψ hc hp

/-- Discharge the minimum and uniqueness premises of the literal degree-21
consumer. The independently constructed character, its marked local values,
the special inductions, and the odd-order spectrum remain explicit inputs. -/
public theorem nonempty_of_induction_character_and_odd_structure (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) (hloc : HasLocalValues D k χ)
    (hodd : ∀ g : G, Odd (orderOf g) →
      orderOf g ∈ ({1, 3, 5, 7, 11} : Finset ℕ)) :
    Nonempty (Degree21Character G) := by
  obtain ⟨hmin, huniq⟩ := minimum_and_unique D k L hcard I
  exact nonempty_of_character_and_odd_structure D k L hcard χ hχ hloc hmin
    (fun θ hθ hd => huniq θ χ hθ hχ hd hloc.degree) hodd

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
