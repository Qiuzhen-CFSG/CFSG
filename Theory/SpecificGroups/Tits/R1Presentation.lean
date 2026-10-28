module

public import Theory.SpecificGroups.Tits.PresentationCosetBounds
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A local presentation covering Parrott's `R₁` subgroup

Remove `r8` and the nine relators involving it from Parrott's presentation.
The resulting nine-generator, 28-relator group maps onto `parrottR1Subgroup`.
We define its words by deleting `r8` from the original free group, and verify
that reinserting the nine remaining generators recovers each original relator
exactly. Thus no additional relation has been imposed on the local subgroup.

The image of the induced homomorphism is the closure of the nine canonical
generators. Consequently any finite upper bound for this local presentation
transfers to `parrottR1Subgroup`, without assuming the full group is finite.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p. 683; see `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits

/-- The nine generators of the local presentation, omitting `r8`. -/
public inductive ParrottR1Generator
  | r1 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8
  deriving DecidableEq

public instance : Fintype ParrottR1Generator :=
  Fintype.ofList [.r1, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]
    (by intro a; cases a <;> simp)

/-- Inclusion of the local generators into the original presentation. -/
@[expose] public def parrottR1GeneratorInclusion : ParrottR1Generator → ParrottGenerator
  | .r1 => .r1
  | .s1 => .s1
  | .s2 => .s2
  | .s3 => .s3
  | .s4 => .s4
  | .s5 => .s5
  | .s6 => .s6
  | .s7 => .s7
  | .s8 => .s8

/-- The 28 original equations that do not contain `r8`. -/
public inductive ParrottR1RelatorIndex
  | i_r1 | i_s1 | i_s2 | i_s4 | i_s6 | i_s8 | i_s3 | i_s5 | i_s7
  | ii_s1_s2 | ii_s1_s3 | ii_s1_s5
  | iii_s1_s6 | iii_s1_s7 | iii_s1_s8
  | iv_s2_s4 | iv_s2_s6 | iv_s2_s8 | iv_s7_s2
  | v_s7_s4 | v_s3_s5 | v_s5_s4
  | vi_s1_r1 | vii_s2 | vii_s4 | vii_s5 | vii_s3 | vii_r3
  deriving DecidableEq

public instance : Fintype ParrottR1RelatorIndex :=
  Fintype.ofList
    [.i_r1, .i_s1, .i_s2, .i_s4, .i_s6, .i_s8, .i_s3, .i_s5, .i_s7,
      .ii_s1_s2, .ii_s1_s3, .ii_s1_s5, .iii_s1_s6, .iii_s1_s7, .iii_s1_s8,
      .iv_s2_s4, .iv_s2_s6, .iv_s2_s8, .iv_s7_s2, .v_s7_s4, .v_s3_s5, .v_s5_s4,
      .vi_s1_r1, .vii_s2, .vii_s4, .vii_s5, .vii_s3, .vii_r3]
    (by intro a; cases a <;> simp)

/-- The exact original equation corresponding to each local equation. -/
@[expose] public def parrottR1RelatorInclusion : ParrottR1RelatorIndex → ParrottRelatorIndex
  | .i_r1 => .i_r1
  | .i_s1 => .i_s1
  | .i_s2 => .i_s2
  | .i_s4 => .i_s4
  | .i_s6 => .i_s6
  | .i_s8 => .i_s8
  | .i_s3 => .i_s3
  | .i_s5 => .i_s5
  | .i_s7 => .i_s7
  | .ii_s1_s2 => .ii_s1_s2
  | .ii_s1_s3 => .ii_s1_s3
  | .ii_s1_s5 => .ii_s1_s5
  | .iii_s1_s6 => .iii_s1_s6
  | .iii_s1_s7 => .iii_s1_s7
  | .iii_s1_s8 => .iii_s1_s8
  | .iv_s2_s4 => .iv_s2_s4
  | .iv_s2_s6 => .iv_s2_s6
  | .iv_s2_s8 => .iv_s2_s8
  | .iv_s7_s2 => .iv_s7_s2
  | .v_s7_s4 => .v_s7_s4
  | .v_s3_s5 => .v_s3_s5
  | .v_s5_s4 => .v_s5_s4
  | .vi_s1_r1 => .vi_s1_r1
  | .vii_s2 => .vii_s2
  | .vii_s4 => .vii_s4
  | .vii_s5 => .vii_s5
  | .vii_s3 => .vii_s3
  | .vii_r3 => .vii_r3

/-- Delete `r8` from a word while preserving the other nine generators. -/
@[expose] public def parrottR1Delete : FreeGroup ParrottGenerator →* FreeGroup ParrottR1Generator :=
  FreeGroup.lift (fun a => match a with
    | .r8 => 1
    | .r1 => FreeGroup.of .r1
    | .s1 => FreeGroup.of .s1
    | .s2 => FreeGroup.of .s2
    | .s3 => FreeGroup.of .s3
    | .s4 => FreeGroup.of .s4
    | .s5 => FreeGroup.of .s5
    | .s6 => FreeGroup.of .s6
    | .s7 => FreeGroup.of .s7
    | .s8 => FreeGroup.of .s8
)

/-- Each local relator is the corresponding original word on nine generators. -/
@[expose] public def parrottR1Relator (i : ParrottR1RelatorIndex) :
    FreeGroup ParrottR1Generator :=
  parrottR1Delete (parrottRelator (parrottR1RelatorInclusion i))

/-- The set of 28 local defining relators. -/
@[expose] public def parrottR1RelatorSet : Set (FreeGroup ParrottR1Generator) :=
  Set.range parrottR1Relator

/-- Reinsertion recovers the original relator, with its exact factor order. -/
public theorem parrottR1Relator_inclusion (i : ParrottR1RelatorIndex) :
    FreeGroup.map parrottR1GeneratorInclusion (parrottR1Relator i) =
      parrottRelator (parrottR1RelatorInclusion i) := by
  cases i <;>
    simp [parrottR1Relator, parrottR1RelatorInclusion, parrottRelator,
      parrottCommutator, parrottR3, parrottR5, parrottR7, parrottR1Delete,
      parrottR1GeneratorInclusion]

/-- The group with the nine generators and exactly the 28 retained relators. -/
@[expose] public def ParrottR1Group := PresentedGroup parrottR1RelatorSet
  deriving Group

/-- The canonical local generators. -/
@[expose] public def parrottR1Generator (a : ParrottR1Generator) : ParrottR1Group :=
  PresentedGroup.of a

/-- The canonical local generators generate the entire local presented group. -/
public theorem parrottR1_closure_range_generator :
    Subgroup.closure (Set.range parrottR1Generator) = ⊤ :=
  PresentedGroup.closure_range_of parrottR1RelatorSet

/-- The subgroup generated by the two involutions `r1` and `s1` in the local group. -/
@[expose] public def parrottR1DihedralSubgroup : Subgroup ParrottR1Group :=
  Subgroup.closure {parrottR1Generator .r1, parrottR1Generator .s1}

/-- The canonical local generators satisfy all 28 retained relations. -/
public theorem parrottR1_generators_satisfy_relations (i : ParrottR1RelatorIndex) :
    FreeGroup.lift parrottR1Generator (parrottR1Relator i) = 1 := by
  have hlift : FreeGroup.lift parrottR1Generator = PresentedGroup.mk parrottR1RelatorSet := by
    ext a
    rfl
  rw [hlift]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- The local presentation maps into Parrott's full presented group. -/
@[expose] public def parrottR1ToParrott : ParrottR1Group →* ParrottGroup :=
  PresentedGroup.map (FreeGroup.map parrottR1GeneratorInclusion) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨parrottR1RelatorInclusion i, (parrottR1Relator_inclusion i).symm⟩)

@[simp] public theorem parrottR1ToParrott_generator (a : ParrottR1Generator) :
    parrottR1ToParrott (parrottR1Generator a) =
      parrottGenerator (parrottR1GeneratorInclusion a) := rfl

private theorem generatorInclusion_range :
    Set.range parrottR1GeneratorInclusion = {a | a ≠ ParrottGenerator.r8} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    cases b <;> decide
  · intro ha
    cases a with
    | r1 => exact ⟨.r1, rfl⟩
    | r8 => exact (ha rfl).elim
    | s1 => exact ⟨.s1, rfl⟩
    | s2 => exact ⟨.s2, rfl⟩
    | s3 => exact ⟨.s3, rfl⟩
    | s4 => exact ⟨.s4, rfl⟩
    | s5 => exact ⟨.s5, rfl⟩
    | s6 => exact ⟨.s6, rfl⟩
    | s7 => exact ⟨.s7, rfl⟩
    | s8 => exact ⟨.s8, rfl⟩

/-- The image is precisely the subgroup generated without `r8`. -/
public theorem parrottR1ToParrott_range :
    parrottR1ToParrott.range = parrottR1Subgroup := by
  have hgenerators :
      parrottR1ToParrott ∘ parrottR1Generator =
        parrottGenerator ∘ parrottR1GeneratorInclusion := rfl
  rw [MonoidHom.range_eq_map, ← parrottR1_closure_range_generator,
    MonoidHom.map_closure, ← Set.range_comp, hgenerators, Set.range_comp,
    generatorInclusion_range]
  rfl

/-- The local presentation, with codomain restricted to the subgroup it generates. -/
@[expose] public def parrottR1ToSubgroup : ParrottR1Group →* parrottR1Subgroup :=
  parrottR1ToParrott.codRestrict parrottR1Subgroup (fun x => by
    rw [← parrottR1ToParrott_range]
    exact ⟨x, rfl⟩)

/-- Every element of `R₁` is represented by the local presentation. -/
public theorem parrottR1ToSubgroup_surjective : Function.Surjective parrottR1ToSubgroup := by
  intro x
  have hx : x.val ∈ parrottR1ToParrott.range := by
    rw [parrottR1ToParrott_range]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

/-- Any finite cardinal bound for the local presentation bounds the actual subgroup. -/
public theorem parrottR1Subgroup_bound_of_local {n : ℕ}
    (h : Finite ParrottR1Group ∧ Nat.card ParrottR1Group ≤ n) :
    Finite parrottR1Subgroup ∧ Nat.card parrottR1Subgroup ≤ n := by
  let := h.1
  exact ⟨Finite.of_surjective _ parrottR1ToSubgroup_surjective,
    (Nat.card_le_card_of_surjective _ parrottR1ToSubgroup_surjective).trans h.2⟩

end Tits
