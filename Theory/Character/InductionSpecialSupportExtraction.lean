module

public import Theory.Character.InductionSpecialSupport
public import Theory.Character.Peterfalvi2
public import Theory.Character.Peterfalvi3

/-!
# Integral induction isometries on a special support

Transporters in the inducing subgroup make induction preserve the scalar
product of supported differences. Virtual-character integrality expands those
images in the ambient irreducible basis, giving exactly the integral isometry
required by Peterfalvi (1.4). Its signed irreducible differences have degree
zero, so the extracted irreducibles have equal degrees.

Source: Peterfalvi, *Character Theory for the Odd Order Theorem*, (1.4),
and the special-set induction argument in Fong, J. Algebra 6 (1967), p. 72.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace Section1
variable {G : Type*} [Group G] [Finite G]

theorem inducedCF_eq_standardInduction (H : Subgroup G) (φ : ClassFunction H) :
    inducedCF H φ = _root_.inducedClassFunction H φ := by
  classical
  funext g
  unfold inducedCF inducedClassFunction _root_.inducedClassFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.inv G)
  intro x
  change (if h : x * g * x⁻¹ ∈ H then φ ⟨_, h⟩ else 0) =
    (if h : x⁻¹⁻¹ * g * x⁻¹ ∈ H then φ ⟨_, h⟩ else 0)
  simp only [inv_inv]

theorem induction_integralIsometry_of_specialSupport
    {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ} [NeZero n]
    (H : Subgroup G) (A : Set H)
    (hA : ∀ a b : H, a ∈ A → b ∈ A →
      ∀ g : G, g⁻¹ * (a : G) * g = (b : G) → g ∈ H)
    (μ : J → ConjClassFunction G) (hμ : IsCompleteIrreducibleCharacterFamily μ)
    (d : J → ℕ) (hd : ∀ j, degree (ofConjClassFunction (μ j)) = (d j : ℂ))
    (hdpos : ∀ j, 0 < d j)
    (χ : Fin n → ClassFunction H) (hχ : IsIrreducibleCharacterBasis χ)
    (hdeg : ∀ i, degree (χ i) = degree (χ 0))
    (hs : ∀ i, _root_.supportedOn (χ i - χ 0) A) :
    IsIntegralIsometryOnCharacterDifferences
      (fun j => ofConjClassFunction (μ j)) d χ (inducedCF H) := by
  classical
  let α := fun i => inducedCF H (χ i - χ 0)
  have hv (i) : IsVirtualCharacter (α i) :=
    Section2.inducedCF_isVirtualCharacter_of_virtualCharacter H
      (Section3.isVirtualCharacter_sub
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hχ.1 i))
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hχ.1 0)))
  have hint (i) (j) : ∃ z : ℤ,
      scalarProduct G (α i) (ofConjClassFunction (μ j)) = (z : ℂ) :=
    scalarProduct_isVirtualCharacter_eq_int (hv i)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hμ.1 j)))
  let c := fun i => Section3.irreducibleBasisCoeff (α i) (hint i)
  obtain ⟨b, hb⟩ := completeFamily_form_basis hμ
  have heval (i) : evalCoeff (fun j => ofConjClassFunction (μ j)) (c i) = α i :=
    Section3.irreducibleBasis_evalCoeff_coeff hμ b hb _
      (isVirtualCharacter_isClassFunction (hv i)) (hint i)
  refine ⟨hd, hdpos, c, ?_, ?_, ?_, fun i => (heval i).symm⟩
  · funext j
    have hh := Section3.irreducibleBasisCoeff_spec (α 0) (hint 0) j
    have hz : α 0 = 0 := by
      ext g
      simp [α, inducedCF, inducedClassFunction]
    change scalarProduct G (α 0) (ofConjClassFunction (μ j)) = (c 0 j : ℂ) at hh
    rw [hz] at hh
    have hc : (c 0 j : ℂ) = 0 := by simpa [scalarProduct] using hh.symm
    exact_mod_cast hc
  · intro i
    rw [degree_inducedClassFunction]
    change (H.index : ℂ) * (degree (χ i) - degree (χ 0)) = 0
    rw [hdeg i, sub_self, mul_zero]
  · intro i j
    rw [← Section3.irreducibleBasis_scalarProduct_evalCoeff hμ, heval i, heval j]
    dsimp [α]
    rw [inducedCF_eq_standardInduction, inducedCF_eq_standardInduction]
    have hc : _root_.IsClassFunction (χ j - χ 0) := by
      intro x g
      change χ j (g * x * g⁻¹) - χ 0 (g * x * g⁻¹) = χ j x - χ 0 x
      rw [isBookIrreducibleCharacter_isClassFunction (χ j)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hχ.1 j)),
        isBookIrreducibleCharacter_isClassFunction (χ 0)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hχ.1 0))]
    exact scalarProduct_inducedClassFunction_of_specialSupport H A hA
      (χ i - χ 0) (χ j - χ 0) hc (hs i) (hs j)

/-- The special-support extraction, including equality of ambient degrees. -/
theorem exists_irreducibles_of_specialSupport
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (H : Subgroup G) (A : Set H)
    (hA : ∀ a b : H, a ∈ A → b ∈ A →
      ∀ g : G, g⁻¹ * (a : G) * g = (b : G) → g ∈ H)
    (χ : Fin n → ClassFunction H) (hχ : IsIrreducibleCharacterBasis χ)
    (hdeg : ∀ i, degree (χ i) = degree (χ 0))
    (hs : ∀ i, _root_.supportedOn (χ i - χ 0) A) :
    ∃ (ε : ℂ), IsSign ε ∧ ∃ μ : Fin n → ClassFunction G,
      IsIrreducibleCharacterBasis μ ∧
      (∀ i, degree (μ i) = degree (μ 0)) ∧
      ∀ i, inducedCF H (χ i - χ 0) = ε • (μ i - μ 0) := by
  classical
  obtain ⟨J, instJ, μ, hμ, b, hb⟩ := irreducible_characters_form_basis (G := G)
  let := instJ
  have hμbasis : IsIrreducibleCharacterBasis (fun j => ofConjClassFunction (μ j)) := by
    refine ⟨fun j => Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hμ.1 j), ?_⟩
    intro i j hij he
    apply hij
    apply hμ.2.2
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    exact congrFun he g
  have hpos : ∀ j, ∃ d : ℕ, 0 < d ∧ degree (ofConjClassFunction (μ j)) = (d : ℂ) := by
    intro j
    obtain ⟨d, ρ, hρ, he⟩ := hμbasis.1 j
    change ofConjClassFunction (μ j) = ρ.character at he
    refine ⟨d, ?_, ?_⟩
    · have hne := Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup _ (hμbasis.1 j)
      change degree (ofConjClassFunction (μ j)) ≠ 0 at hne
      rw [he, degree_representation_character] at hne
      have : d ≠ 0 := by simpa using hne
      omega
    · rw [he, degree_representation_character]
      simp
  choose d hdpos hd using hpos
  have hiso := induction_integralIsometry_of_specialSupport H A hA μ hμ d hd hdpos χ hχ hdeg hs
  have horth : IsOrthonormalFamily χ := by
    exact scalarProduct_isBookIrreducible_family χ
      (fun i => isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hχ.1 i)) hχ.2
  obtain ⟨ε, hε, ν, hν, he⟩ := proposition_1_4_source hn
    (fun j => ofConjClassFunction (μ j)) hμbasis d χ hχ hdeg horth (inducedCF H) hiso
  refine ⟨ε, hε, ν, hν, ?_, he⟩
  intro i
  have hh := congrArg degree (he i)
  rw [degree_inducedClassFunction] at hh
  have hd0 : degree (χ i - χ 0) = 0 := sub_eq_zero.mpr (hdeg i)
  rw [hd0, mul_zero] at hh
  have hh' : ε * (degree (ν i) - degree (ν 0)) = 0 := hh.symm
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_left hε0)
end Section1
