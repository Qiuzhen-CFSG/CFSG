module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Normalization

/-!
# A finite presentation for the remaining central-lift calculation

Impose commutation of each of Parrott's 37 relator words with each of the ten
generators, together with the ten correction-word equations. These are 380
relations. Every normalized tuple in a central extension of the Parrott group
satisfies them, so it is an image of this presentation. The original 37
relations are not imposed here: proving them in this group is the remaining
nonabelian calculation, and then the displayed homomorphism transports them
to the canonical universal cover. The final reductions use the ten correction
equations to recover three root relations and seven Weyl relations; only the
twenty selected power/root equations and seven selected Weyl equations remain.

Source: Parrott (1972), §5, p.683; the normalization is proved in the imported
module. This auxiliary presentation is not asserted to be the Tits group.
-/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- The 370 centrality equations and ten normalization equations. -/
abbrev NormalizedRelatorIndex :=
  (ParrottRelatorIndex × ParrottGenerator) ⊕ ParrottGenerator

/-- Only centrality and normalization are relations of this auxiliary presentation. -/
@[expose] def normalizedRelator : NormalizedRelatorIndex → FreeGroup ParrottGenerator
  | .inl (j, i) => parrottCommutator (parrottRelator j) (FreeGroup.of i)
  | .inr i => correctionWord i

/-- The set of the 380 auxiliary relators. -/
@[expose] def normalizedRelatorSet : Set (FreeGroup ParrottGenerator) :=
  Set.range normalizedRelator

/-- The finite presentation to which the residual word calculations apply. -/
@[expose] def NormalizedPresentation := PresentedGroup normalizedRelatorSet
  deriving Group

/-- The literal free-generator images in the auxiliary presentation. -/
@[expose] def normalizedGenerator (i : ParrottGenerator) : NormalizedPresentation :=
  PresentedGroup.of i

/-- Any tuple satisfying centrality and the ten normalization equations gives
an actual homomorphism from the auxiliary presentation. -/
def normalizedLift {E : Type*} [Group E] (g : ParrottGenerator → E)
    (hc : ∀ j, FreeGroup.lift g (parrottRelator j) ∈ Subgroup.center E)
    (hn : ∀ i, FreeGroup.lift g (correctionWord i) = 1) :
    NormalizedPresentation →* E :=
  PresentedGroup.toGroup (by
    rintro _ ⟨j | i, rfl⟩
    · rcases j with ⟨j, i⟩
      change FreeGroup.lift g
        (parrottCommutator (parrottRelator j) (FreeGroup.of i)) = 1
      simp only [parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
      have he := ((hc j).comm (g i)).inv_inv.commutator_eq
      simpa only [commutatorElement_def, inv_inv] using he
    · exact hn i)

/-- The auxiliary presentation homomorphism preserves the named generators. -/
@[simp] theorem normalizedLift_generator {E : Type*} [Group E]
    (g : ParrottGenerator → E)
    (hc : ∀ j, FreeGroup.lift g (parrottRelator j) ∈ Subgroup.center E)
    (hn : ∀ i, FreeGroup.lift g (correctionWord i) = 1) (i : ParrottGenerator) :
    normalizedLift g hc hn (normalizedGenerator i) = g i :=
  PresentedGroup.toGroup.of _

/-- A proved source relation in the auxiliary presentation holds for every
normalized central tuple, with the original relator and commutator convention. -/
theorem relation_of_normalizedPresentation {E : Type*} [Group E]
    (g : ParrottGenerator → E)
    (hc : ∀ j, FreeGroup.lift g (parrottRelator j) ∈ Subgroup.center E)
    (hn : ∀ i, FreeGroup.lift g (correctionWord i) = 1)
    (j : ParrottRelatorIndex)
    (h : FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    FreeGroup.lift g (parrottRelator j) = 1 := by
  have he : (normalizedLift g hc hn).comp (FreeGroup.lift normalizedGenerator) =
      FreeGroup.lift g := by
    ext i
    simp
  have hj := congrArg (normalizedLift g hc hn) h
  change ((normalizedLift g hc hn).comp (FreeGroup.lift normalizedGenerator))
    (parrottRelator j) = normalizedLift g hc hn 1 at hj
  simpa only [he, map_one] using hj

/-- Relation groups I--V contain the ten power and thirteen root equations. -/
@[expose] def isPowerRootRelator : ParrottRelatorIndex → Bool
  | .vi_r1_r8 | .vi_s1_r1 | .vi_r8_s8
  | .vii_s2 | .vii_s4 | .vii_s5 | .vii_s3 | .vii_r3
  | .viii_s2 | .viii_s4 | .viii_s1 | .viii_s7 | .viii_s3 | .viii_r3 => false
  | _ => true


/-- The normalization equations are defining relations of the auxiliary presentation. -/
theorem normalizedGenerator_correctionWord (i : ParrottGenerator) :
    FreeGroup.lift normalizedGenerator (correctionWord i) = 1 := by
  have hh : FreeGroup.lift normalizedGenerator = PresentedGroup.mk normalizedRelatorSet := by
    ext j
    rfl
  rw [hh]
  exact PresentedGroup.one_of_mem ⟨.inr i, rfl⟩

/-- The twenty power/root equations left after three correction identities are used. -/
@[expose] def isPowerRootSeed : ParrottRelatorIndex → Bool
  | .iii_s1_s7 | .iv_s2_s8 | .iv_s7_s2 => false
  | j => isPowerRootRelator j

/-- Seven Weyl equations suffice once the power/root equations hold. -/
@[expose] def isWeylSeed : ParrottRelatorIndex → Bool
  | .vi_r1_r8 | .vii_s4 | .vii_s5 | .vii_s3 | .vii_r3 | .viii_s2 | .viii_s4 => true
  | _ => false

/-- The correction words for s₂, s₄ and s₆ recover the three omitted root equations. -/
theorem powerRoot_relations_of_seed
    (hseed : ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  have hiii7 : FreeGroup.lift normalizedGenerator (parrottRelator .iii_s1_s7) = 1 := by
    simpa [correctionWord, hseed .v_s7_s4 rfl] using normalizedGenerator_correctionWord .s2
  have hiv7 : FreeGroup.lift normalizedGenerator (parrottRelator .iv_s7_s2) = 1 := by
    simpa [correctionWord, hseed .v_s7_s4 rfl, hseed .v_s5_s4 rfl] using
      normalizedGenerator_correctionWord .s4
  have hiv8 : FreeGroup.lift normalizedGenerator (parrottRelator .iv_s2_s8) = 1 := by
    simpa [correctionWord, hiv7, hseed .v_s7_s4 rfl, hseed .v_s5_s4 rfl] using
      normalizedGenerator_correctionWord .s6
  intro j hj
  cases j <;> first | exact hseed _ rfl | exact hiii7 | exact hiv7 | exact hiv8 | cases hj

/-- The other seven correction words recover every omitted Weyl equation,
including the source fifth- and third-power relations. -/
theorem relations_of_powerRoot_and_weyl_seed
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hweyl : ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    SatisfiesParrottRelations normalizedGenerator := by
  have hvii2 : FreeGroup.lift normalizedGenerator (parrottRelator .vii_s2) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .iii_s1_s7 rfl,
      hroot .v_s7_s4 rfl] using normalizedGenerator_correctionWord .s8
  have hviii7 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s7) = 1 := by
    simpa [correctionWord, hroot .iii_s1_s8 rfl, hroot .v_s5_s4 rfl,
      hweyl .viii_s4 rfl] using normalizedGenerator_correctionWord .s1
  have hvi1 : FreeGroup.lift normalizedGenerator (parrottRelator .vi_s1_r1) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .i_r8 rfl, hroot .iii_s1_s8 rfl,
      hroot .v_s5_s4 rfl, hweyl .vii_s5 rfl, hviii7] using
      normalizedGenerator_correctionWord .r1
  have hvi8 : FreeGroup.lift normalizedGenerator (parrottRelator .vi_r8_s8) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .iii_s1_s7 rfl,
      hroot .v_s7_s4 rfl, hvii2, hweyl .viii_s4 rfl] using
      normalizedGenerator_correctionWord .r8
  have hviii3 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s3) = 1 := by
    simpa [correctionWord, hroot .i_s1 rfl, hroot .v_s5_s4 rfl,
      hweyl .vii_s3 rfl, hweyl .viii_s4 rfl] using normalizedGenerator_correctionWord .s3
  have hviii1 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s1) = 1 := by
    simpa [correctionWord, hroot .iii_s1_s8 rfl, hroot .v_s5_s4 rfl,
      hweyl .vii_s5 rfl, hweyl .vii_s3 rfl, hweyl .viii_s4 rfl, hviii3] using
      normalizedGenerator_correctionWord .s5
  have hviiir3 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hweyl .vii_r3 rfl, hviii1, hviii7, hviii3] using
      normalizedGenerator_correctionWord .s7
  intro j
  cases j <;> first | exact hroot _ rfl | exact hweyl _ rfl | assumption

end Tits.CentralCoverLifting.CompatibleGenerators
