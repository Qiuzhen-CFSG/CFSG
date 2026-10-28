module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Complete
public import Theory.Representation.JankoTwo.SmallBinaryDegrees
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion

/-!
# Nonbinary traces and binary degrees for the Hall--Janko source module

The checked six- and fourteen-dimensional Frobenius pairs have nonbinary
traces. Together with the five larger modules and the trivial module they
exhaust the simple modules by the actual bound of ten odd conjugacy classes.
Transport through that exhaustion proves nonbinary traces for every simple
module in the small window. Scalar extension and the existing Schur-field
calculation then force binary degrees twelve or twenty-eight.

This closes the degree-fourteen trace premise without a further binary
exclusion certificate. The final binary-degree consumer retains the original
faithful irreducible action of the literal J2 carrier.

Source: GM02, Proposition 5.1, manuscript p.16; Aschbacher--Smith K.4,
printed pp.457--460. Matrix provenance is retained in ModularCertificate.
-/

public noncomputable section
open scoped TensorProduct
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2
open ModularCertificate ModularCertificate.SmallModels
open ModularCertificate.SmallModels.Arithmetic
open G2FourModule.Embedding.InnerRealization
universe v

private theorem pair_with_trace {n : ℕ} [NeZero n]
    (A B : CodeMatrix n) (w : List Bool) (c : Fin 4) (hc : c = 2 ∨ c = 3)
    (hcert : ParameterCertificate.{v} A B w c)
    (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2] :
    ∃ ρ σ : Representation F Carrier (Fin n → F),
      IsIrreducible ρ ∧ IsIrreducible σ ∧ IsEmpty (ρ.Equiv σ) ∧
      (∃ g, ρ.character g ^ 2 ≠ ρ.character g) ∧
      (∃ g, σ.character g ^ 2 ≠ σ.character g) := by
  let hp := PresentationExact.toCarrier_injective
  obtain ⟨t, ht⟩ := exists_parameter (F := F)
  obtain ⟨hr, hd, htr⟩ := hcert F t ht
  obtain ⟨hr', hd', htr'⟩ := hcert F (t ^ 2) (square_parameter t ht)
  refine ⟨action hp _ _ hr, action hp _ _ hr', action_irreducible hp _ _ hr hd,
    action_irreducible hp _ _ hr' hd', ⟨?_⟩, ?_, ?_⟩
  · intro e
    have he := congrFun (Representation.char_iso e) (wordValue GeneratorPair.a GeneratorPair.b w)
    rw [character_word, character_word, htr, htr'] at he
    exact coefficient_ne_square t ht c hc he
  · refine ⟨wordValue GeneratorPair.a GeneratorPair.b w, ?_⟩
    rw [character_word, htr, ← coefficient_frobenius]
    exact (coefficient_ne_square t ht c hc).symm
  · refine ⟨wordValue GeneratorPair.a GeneratorPair.b w, ?_⟩
    rw [character_word, htr', ← coefficient_frobenius]
    exact (coefficient_ne_square (t ^ 2) (square_parameter t ht) c hc).symm

private theorem smallModels_with_trace
    (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2] :
    ∃ (ρ : ∀ i, Representation F Carrier (Fin (smallDegree i) → F)),
      (∀ i, IsIrreducible (ρ i)) ∧
      (Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) ∧
      ∀ i, ∃ g, (ρ i).character g ^ 2 ≠ (ρ i).character g := by
  obtain ⟨ρ₆, σ₆, hρ₆, hσ₆, hne₆, htr₆, htr₆'⟩ :=
    pair_with_trace SixData.A SixData.B SixData.traceWord SixData.traceCode
      SixData.traceCode_nonbinary six_parameterCertificate F
  obtain ⟨ρ₁₄, σ₁₄, hρ₁₄, hσ₁₄, hne₁₄, htr₁₄, htr₁₄'⟩ :=
    pair_with_trace FourteenData.A FourteenData.B FourteenData.traceWord FourteenData.traceCode
      FourteenData.traceCode_nonbinary fourteen_parameterCertificate F
  let ρ : ∀ i, Representation F Carrier (Fin (smallDegree i) → F) :=
    Fin.cases ρ₆ (Fin.cases σ₆ (Fin.cases ρ₁₄ (Fin.cases σ₁₄ (fun i => Fin.elim0 i))))
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hρ₆
    · exact hσ₆
    · exact hρ₁₄
    · exact hσ₁₄
  · intro i j hij
    constructor
    intro e
    have hd := e.toLinearEquiv.finrank_eq
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hij rfl
      | exact hne₆.false e
      | exact hne₆.false e.symm
      | exact hne₁₄.false e
      | exact hne₁₄.false e.symm
      | norm_num [smallDegree] at hd
  · intro i
    fin_cases i
    · exact htr₆
    · exact htr₆'
    · exact htr₁₄
    · exact htr₁₄'

private theorem small_bounds (i : Fin 4) : 6 ≤ smallDegree i ∧ smallDegree i ≤ 14 := by
  revert i
  decide

private theorem large_lower (i : Fin 5) : 36 ≤ largeDegree i := by
  revert i
  decide

private abbrev CandidateIndex := Option (Fin 4 ⊕ Fin 5)

/-- The native simple-count certificate transfers the checked nonbinary traces. -/
theorem closed_small_trace
    (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
    {U : Type v} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (τ : Representation F Carrier U) [IsIrreducible τ]
    (hd : Module.finrank F U = 6 ∨ Module.finrank F U = 14) :
    ∃ g, τ.character g ^ 2 ≠ τ.character g := by
  classical
  obtain ⟨ρs, hsirr, hsne, hstrace⟩ := smallModels_with_trace F
  obtain ⟨ρl, hlirr, hlne⟩ := ModularCertificate.largeModelsExist F
  let V : CandidateIndex → Type v := fun i => match i with
    | none => F
    | some (.inl j) => Fin (smallDegree j) → F
    | some (.inr j) => Fin (largeDegree j) → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F Carrier (V i) := fun i => match i with
    | none => Representation.trivial F Carrier F
    | some (.inl j) => ρs j
    | some (.inr j) => ρl j
  have finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    rcases i with _ | (i | i)
    · change IsIrreducible (Representation.trivial F Carrier F)
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    · exact hsirr i
    · exact hlirr i
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    have he := e.toLinearEquiv.finrank_eq
    rcases i with _ | (i | i) <;> rcases j with _ | (j | j)
    all_goals simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at he
    · exact hij rfl
    · have := small_bounds j; omega
    · have := large_lower j; omega
    · have := small_bounds i; omega
    · exact (hsne (fun h => hij (by rw [h]))).false e
    · have := small_bounds i
      have := large_lower j
      omega
    · have := large_lower i; omega
    · have := large_lower i
      have := small_bounds j
      omega
    · exact (hlne (fun h => hij (by rw [h]))).false e
  have hc : Nat.card CandidateIndex = 10 := by
    simp [CandidateIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_pRegular_class_bound V rep 2 hdistinct
    (hc ▸ ModularCertificate.pRegular_class_bound_le_ten) τ
  have he := e.toLinearEquiv.finrank_eq
  rcases i with _ | (i | i)
  · simp only [V, Module.finrank_self] at he
    omega
  · obtain ⟨g, hg⟩ := hstrace i
    refine ⟨g, ?_⟩
    have ht := congrFun (Representation.char_iso e) g
    simpa only [ht] using hg
  · simp only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
    have := large_lower i
    omega


/-- Every absolutely irreducible degree-fourteen action has a nonbinary trace. -/
theorem fourteenTraceSeparation_complete : FourteenTraceSeparation.{v} := by
  intro K _ _ _ U _ _ _ τ _ hi hd
  let C := AlgebraicClosure K
  let σ := extendScalars C τ
  let : IsIrreducible σ := hi.irreducible_of_closure
  have hdim : Module.finrank C (C ⊗[K] U) = 14 := by
    simpa only [Module.finrank_baseChange] using hd
  obtain ⟨g, hg⟩ := closed_small_trace C σ (Or.inr hdim)
  refine ⟨g, ?_⟩
  intro h
  apply hg
  change LinearMap.trace C _ ((τ g).baseChange C) ^ 2 =
    LinearMap.trace C _ ((τ g).baseChange C)
  rw [LinearMap.trace_baseChange, ← map_pow]
  exact congrArg (algebraMap K C) h

/-- The actual degree, fusion and trace contracts, with every premise discharged. -/
theorem absoluteWindowCalculations_complete : AbsoluteWindowCalculations.{v} :=
  calculations_of_degree_fusion_fourteen ModularCertificate.degreeWindow
    powerFusion fourteenTraceSeparation_complete

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow

namespace Representation.JankoTwo.SmallBinaryDegrees
open Sporadic.LeechRelated.J2

/-- The original binary action has degree twelve or twenty-eight throughout
its faithful irreducible degree-thirty-two window. -/
theorem finrank_twelve_or_twentyEight
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Carrier W) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (hd : Module.finrank (ZMod 2) W ≤ 32) :
    Module.finrank (ZMod 2) W = 12 ∨ Module.finrank (ZMod 2) W = 28 :=
  finrank_cases_of_absolute_calculations AbsoluteWindow.absoluteWindowCalculations_complete
    σ hf hi hd

/-- In particular the smaller window needed by the B.4 FF source is degree twelve. -/
theorem finrank_twelve_of_lt_twentyEight
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Carrier W) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (hd : Module.finrank (ZMod 2) W < 28) :
    Module.finrank (ZMod 2) W = 12 := by
  rcases finrank_twelve_or_twentyEight σ hf hi (by omega) with h | h
  · exact h
  · omega

end Representation.JankoTwo.SmallBinaryDegrees
