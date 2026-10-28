module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Values
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Vanishing
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.SporadicFilters
public import CFSG.KnownSimple.UnitaryRankOne
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Complete catalogue analysis for the conditional I.1.3 table

Every constructor of the full known-simple catalogue is analysed here,
including all six classical families, six exceptional extension families,
four small derived carriers, and all twenty-six sporadics. Perfectness
eliminates the cyclic constructor. Completed kernel and rank results are
used directly. The remaining individual model computations and family
restrictions are precisely `KernelInputs` and `RankInputs`.

The output is the actual exhaustive iff and all six kernel isomorphisms,
not a classification hypothesis or a projection from an assumed table.
This is a conditional source assembly: its two collections of individual
inputs must still be instantiated before the unconditional I.1.3 claim.
Source: Aschbacher--Smith I.1.3, printed p.407, with the A.2 rank arguments.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open PerfectCentralCovering
universe u

/-- Both supported degree-three domains supply the source prime-power witness. -/
theorem DegreeThreeParameters.exists_prime_pow {q : ℕ} (h : DegreeThreeParameters q) :
    ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ q = p ^ f := by
  rcases h with ⟨n, hn, hq⟩ | ⟨p, f, hp, _, hf, hq⟩
  · exact ⟨2, n, by decide, hn, hq⟩
  · exact ⟨p, f, hp, by rcases hf with rfl | rfl <;> decide, hq⟩

variable {S : Type u} [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S]

/-- The full linear degree-three branch, including its two exceptional binary endpoints. -/
theorem calculated_psl3_of_inputs (K : KernelInputs S) (R : RankInputs S)
    {q : ℕ} (hS : ClassicalGroup.IsPSL S 3 q) : Calculated S := by
  classical
  by_cases h2 : q = 2
  · exact calculated_psl3_two (h2 ▸ hS)
  by_cases h4 : q = 4
  · subst q
    exact Or.inr ⟨.exceptionalFortyEight, hS, K.linearThreeFour hS⟩
  have hk := K.linearThree q (R.linearThree q hS) h2 h4 hS
  by_cases hq : q % 3 = 1
  · have he : Nonempty (schurMultiplier S ≃* MultiplierShape.three.Carrier) := by
      simpa only [hq, ↓reduceIte] using hk
    exact Or.inr ⟨.three,
      ⟨not_linearThreeFour_of_multiplier_three K he, Or.inl ⟨q, hq, hS⟩⟩, he⟩
  · exact Or.inl (by simpa only [hq, ↓reduceIte] using hk)

omit [Finite S] in
/-- The unitary branch preserves q as the fixed-field order throughout. -/
theorem calculated_psu3_of_inputs (K : KernelInputs S) (R : RankInputs S)
    {q : ℕ} (hS : ClassicalGroup.IsPSU S 3 q) : Calculated S := by
  classical
  have h2 : q ≠ 2 := fun hq2 => not_psu3_two (hq2 ▸ hS)
  have hp := R.unitaryThree q hS
  have hk := K.unitaryThree q hp h2 hS
  by_cases hq : q % 3 = 2
  · have he : Nonempty (schurMultiplier S ≃* MultiplierShape.three.Carrier) := by
      simpa only [hq, ↓reduceIte] using hk
    obtain ⟨p, f, hprime, hf, rfl⟩ := hp.exists_prime_pow
    exact Or.inr ⟨.three,
      ⟨not_linearThreeFour_of_multiplier_three K he, Or.inr ⟨p, f, hprime, hf, hq, hS⟩⟩, he⟩
  · exact Or.inl (by simpa only [hq, ↓reduceIte] using hk)

/-- Linear dimensions are reduced by the individual simple-model rank input. -/
theorem calculated_linear_of_inputs (K : KernelInputs S) (R : RankInputs S)
    {n q : ℕ} (hp : KnownSimple.LinearParameters n q)
    (hS : ClassicalGroup.IsPSL S n q) : Calculated S := by
  rcases R.linear n q hp hS with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact calculated_psl2 (hp.2.2 rfl) hS
  · exact calculated_psl3_of_inputs K R hS
  · exact Or.inr ⟨.two, Or.inl hS, LieMultipliers.PSL4Two.schurMultiplier_equiv_two hS⟩
  · exact Or.inl (multiplier_psl5_two hS)

omit [Finite S] [Group.IsPerfect S] [IsSimpleGroup S] in
/-- Rank-one symplectic models are identified by the literal central-quotient equivalence. -/
theorem isPSL_of_psp_rank_one {q : ℕ} (h : ClassicalGroup.IsPSp S 1 q) :
    ClassicalGroup.IsPSL S 2 q := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩

/-- Symplectic survivors use the proved even four-space vanishing formula. -/
theorem calculated_symplectic_of_inputs (R : RankInputs S)
    {r q : ℕ} (hp : KnownSimple.SymplecticParameters r q)
    (hS : ClassicalGroup.IsPSp S r q) : Calculated S := by
  rcases R.symplectic r q hp hS with ⟨rfl, hq⟩ | ⟨rfl, n, hn, rfl⟩
  · exact calculated_psl2 hq (isPSL_of_psp_rank_one hS)
  · exact Or.inl (multiplier_psp4_even hn hS)

/-- Every constructor of the complete classical catalogue has its literal consumer. -/
theorem calculated_classical_of_inputs (K : KernelInputs S) (R : RankInputs S)
    (h : KnownSimple.IsClassicalModel S) : Calculated S := by
  cases h with
  | linear n q hp he => exact calculated_linear_of_inputs K R hp he
  | unitary n q hp he =>
      rcases R.unitary n q hp he with rfl | rfl
      · exact calculated_psl2 (hp.2.2.1 rfl) (he.isPSL_two hp.1)
      · exact calculated_psu3_of_inputs K R he
  | symplectic r q hp he => exact calculated_symplectic_of_inputs R hp he
  | orthogonalPlus r q hp he =>
      obtain ⟨hparam, hmodel⟩ := R.orthogonalPlus r q hp he
      exact calculated_linear_of_inputs K R hparam hmodel
  | orthogonalOdd r q hp he =>
      rcases R.orthogonalOdd r q hp he with ⟨hparam, hmodel⟩ | ⟨hparam, hmodel⟩
      · exact calculated_psl2 hparam hmodel
      · exact calculated_symplectic_of_inputs R hparam hmodel
  | orthogonalMinus r q hp he =>
      obtain ⟨hparam, hmodel⟩ := R.orthogonalMinus r q hp he
      exact calculated_psl2 hparam hmodel

omit [IsSimpleGroup S] in
/-- The complete ordinary G₂ constructor keeps field four separate from both vanishing ranges. -/
theorem calculated_g2_of_inputs (K : KernelInputs S) (R : RankInputs S)
    (h : KnownSimple.IsG2Carrier S) : Calculated S := by
  obtain ⟨F, hF, hfin, hlarge, he⟩ := h
  let := hF
  let := hfin
  have hm : ClassificationModels.IsG2At S (Nat.card F) := ⟨F, hF, hfin, rfl, he⟩
  rcases R.g2 (Nat.card F) hlarge hm with ⟨n, hn, hcard⟩ | ⟨hp, hp3⟩
  · by_cases h2 : n = 2
    · have h4 : ClassificationModels.IsG2At S 4 := by simpa only [hcard, h2, show (2 : ℕ) ^ 2 = 4 from rfl] using hm
      exact Or.inr ⟨.two, Or.inr (Or.inl h4), K.g2Four h4⟩
    · exact Or.inl (multiplier_g2_even (by omega : 3 ≤ n) (hcard ▸ hm))
  · exact Or.inl (multiplier_g2_odd_prime hp hp3 hm)

omit [Finite S] [Group.IsPerfect S] [IsSimpleGroup S] in
/-- The six exceptional extension constructors are individually excluded by their rank inputs. -/
theorem not_exceptional_of_inputs (R : RankInputs S) :
    ¬ KnownSimple.IsExceptionalExtensionModel S := by
  intro h
  cases h with
  | f4 q h => exact R.f4 q h
  | e6 q h => exact R.e6 q h
  | e7 q h => exact R.e7 q h
  | e8 q h => exact R.e8 q h
  | twistedE6 q h => exact R.twistedE6 q h
  | reeG2 q h => exact R.reeG2 q h

omit [IsSimpleGroup S] in
/-- All four conventional small derived carriers, without identifying full G₂(2) with its derived group. -/
theorem calculated_smallDerived_of_inputs (K : KernelInputs S)
    (h : KnownSimple.IsSmallDerivedCarrier S) : Calculated S := by
  cases h with
  | symplectic he =>
      let e := he.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
      exact Or.inr ⟨.six, Or.inl ⟨e⟩, multiplier_a6 e⟩
  | g2 he => exact Or.inl (multiplier_g2Derived_of_unitary_three K he.some)
  | ree he => exact Or.inl (K.reeDerived he)
  | tits he => exact Or.inl (K.tits he)

/-- All twenty-six sporadic constructors: values, vanishing, or a genuine rank exclusion. -/
theorem calculated_sporadic_of_inputs (K : KernelInputs S) (R : RankInputs S)
    (hs : IsStronglyQuasithin S) (h : KnownSimple.IsSporadicCarrier S) : Calculated S := by
  obtain ⟨name, he⟩ := h
  cases name with
  | m11 => exact Or.inl (K.m11 he)
  | m12 => exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inl he)), K.m12 he⟩
  | m22 => exact Or.inr ⟨.twelve, he, K.m22 he⟩
  | m23 => exact Or.inl (K.m23 he)
  | m24 => exact Or.inl (K.m24 he)
  | j1 => exact Or.inl (K.j1 he)
  | j2 => exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inr (Or.inl he))), K.j2 he⟩
  | j3 => exact (not_sqt_j3 he.some hs).elim
  | j4 => exact Or.inl (K.j4 he)
  | hs => exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))), K.hs he⟩
  | mcl => exact (not_sqt_mcl he.some hs).elim
  | he => exact Or.inl (K.he he)
  | ru => exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))), K.ru he⟩
  | suz => exact (R.suz he).elim
  | onan => exact (not_sqt_onan he.some hs).elim
  | co1 => exact (R.co1 he).elim
  | co2 => exact (R.co2 he).elim
  | co3 => exact (RankFilters.Leech.co3_not_stronglyQuasithin_of_equiv he.some hs).elim
  | fi22 => exact (R.fi22 he).elim
  | fi23 => exact (R.fi23 he).elim
  | fi24Prime => exact (R.fi24Prime he).elim
  | hn => exact (not_sqt_hn he.some hs).elim
  | ly => exact (R.ly he).elim
  | th => exact (R.th he).elim
  | babyMonster => exact (not_sqt_babyMonster he.some hs).elim
  | monster => exact (RankFilters.Monster.not_stronglyQuasithin_of_equiv he.some hs).elim

/-- The K hypothesis yields the full catalogue, whose every constructor is handled. -/
theorem calculated_of_model_inputs (K : KernelInputs S) (R : RankInputs S)
    (h : IsSQTK KnownSimple.IsKnownSimple S) : Calculated S := by
  have hc := KnownSimple.isKnownSimple_iff_carrier.mp h.isKGroup.mem
  cases hc with
  | cyclic he => exact (not_primeCyclic he).elim
  | alternating n hn he => exact calculated_alternating hn h.stronglyQuasithin he.some
  | classical he => exact calculated_classical_of_inputs K R he
  | g2 he => exact calculated_g2_of_inputs K R he
  | suzuki m hm he =>
      by_cases h1 : m = 1
      · subst m
        exact Or.inr ⟨.elementaryFour, he, K.suzukiEight he⟩
      · exact Or.inl (K.suzukiOther m (by omega) he)
  | exceptional he => exact (not_exceptional_of_inputs R he).elim
  | triality he => exact Or.inl (K.triality he)
  | reeF4 he => exact Or.inl (K.reeF4 he)
  | smallDerived he => exact calculated_smallDerived_of_inputs K he
  | sporadic he => exact calculated_sporadic_of_inputs K R h.stronglyQuasithin he

/-- Conditional I.1.3: full exhaustiveness and all six values follow from the
individual outstanding model facts, using the complete concrete catalogue. -/
theorem table_of_model_inputs (K : KernelInputs S) (R : RankInputs S)
    (h : IsSQTK KnownSimple.IsKnownSimple S) : MultiplierTable S :=
  table_of_calculated (calculated_of_model_inputs K R h) (values_of_model_inputs K R)

end CFSG.Quasithin.ChapterI.SQTKMultipliers
