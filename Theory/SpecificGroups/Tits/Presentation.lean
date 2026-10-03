module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Data.Fintype.OfMap

/-!

# Parrott's presentation of the Tits group

The model `Tits.ParrottGroup` is the group presented by the ten generators and
37 relators in David Parrott, “A Characterization of the Tits' Simple Group”,
Canadian Journal of Mathematics 24 (1972), §5, p. 683. The three additional
symbols `r₃`, `r₅`, and `r₇` denote words, not further generators. The defining
words use the source's commutator convention `a⁻¹ * b⁻¹ * a * b`.

The universal property says that an assignment satisfying precisely these
relators extends uniquely to a homomorphism from the model. This follows by
factoring the free-group lift through the normal closure of the relators;
uniqueness follows from the generator equations. The canonical generators
themselves satisfy all defining relators. The generator and relator bodies
are deliberately exposed so later proofs can check the individual source
equations. Finiteness, simplicity, and ambient-group recognition are separate
results and are not assumptions in this construction.

The scan-checked source and its generator correspondence for the recognition
proof are recorded in
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits

/-- The ten generators in Parrott's presentation. -/
public inductive ParrottGenerator
  | r1 | r8 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8
  deriving DecidableEq

public instance : Fintype ParrottGenerator :=
  Fintype.ofList [.r1, .r8, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]
    (by intro a; cases a <;> simp)

/-- One index for each of the 37 equations on Parrott's p. 683.
The initial roman numeral is the corresponding source relation group. -/
public inductive ParrottRelatorIndex
  | i_r1 | i_r8 | i_s1 | i_s2 | i_s4 | i_s6 | i_s8 | i_s3 | i_s5 | i_s7
  | ii_s1_s2 | ii_s1_s3 | ii_s1_s5
  | iii_s1_s6 | iii_s1_s7 | iii_s1_s8
  | iv_s2_s4 | iv_s2_s6 | iv_s2_s8 | iv_s7_s2
  | v_s7_s4 | v_s3_s5 | v_s5_s4
  | vi_r1_r8 | vi_s1_r1 | vi_r8_s8
  | vii_s2 | vii_s4 | vii_s5 | vii_s3 | vii_r3
  | viii_s2 | viii_s4 | viii_s1 | viii_s7 | viii_s3 | viii_r3
  deriving DecidableEq

public instance : Fintype ParrottRelatorIndex :=
  Fintype.ofList
    [.i_r1, .i_r8, .i_s1, .i_s2, .i_s4, .i_s6, .i_s8, .i_s3, .i_s5, .i_s7,
      .ii_s1_s2, .ii_s1_s3, .ii_s1_s5,
      .iii_s1_s6, .iii_s1_s7, .iii_s1_s8,
      .iv_s2_s4, .iv_s2_s6, .iv_s2_s8, .iv_s7_s2,
      .v_s7_s4, .v_s3_s5, .v_s5_s4,
      .vi_r1_r8, .vi_s1_r1, .vi_r8_s8,
      .vii_s2, .vii_s4, .vii_s5, .vii_s3, .vii_r3,
      .viii_s2, .viii_s4, .viii_s1, .viii_s7, .viii_s3, .viii_r3]
    (by intro i; cases i <;> simp)

/-- The element commutator convention used in Parrott's source. -/
@[expose] public def parrottCommutator {G : Type*} [Group G] (a b : G) : G :=
  a⁻¹ * b⁻¹ * a * b

local notation "r₁" => FreeGroup.of ParrottGenerator.r1
local notation "r₈" => FreeGroup.of ParrottGenerator.r8
local notation "s₁" => FreeGroup.of ParrottGenerator.s1
local notation "s₂" => FreeGroup.of ParrottGenerator.s2
local notation "s₃" => FreeGroup.of ParrottGenerator.s3
local notation "s₄" => FreeGroup.of ParrottGenerator.s4
local notation "s₅" => FreeGroup.of ParrottGenerator.s5
local notation "s₆" => FreeGroup.of ParrottGenerator.s6
local notation "s₇" => FreeGroup.of ParrottGenerator.s7
local notation "s₈" => FreeGroup.of ParrottGenerator.s8

/-- The named word `r₃ = s₁ s₂ s₃²` in Parrott's presentation. -/
@[expose] public def parrottR3 : FreeGroup ParrottGenerator := s₁ * s₂ * s₃ ^ 2

/-- The named word `r₅ = s₁ s₅²` in Parrott's presentation. -/
@[expose] public def parrottR5 : FreeGroup ParrottGenerator := s₁ * s₅ ^ 2

/-- The named word `r₇ = r₃ s₃ s₅ s₇` in Parrott's presentation. -/
@[expose] public def parrottR7 : FreeGroup ParrottGenerator :=
  parrottR3 * s₃ * s₅ * s₇

/-- The 37 relators, each equation `w = v` encoded as `w * v⁻¹`.
The ordering of products and the commutator convention match the source. -/
@[expose] public def parrottRelator : ParrottRelatorIndex → FreeGroup ParrottGenerator
  -- (I)
  | .i_r1 => r₁ ^ 2
  | .i_r8 => r₈ ^ 2
  | .i_s1 => s₁ ^ 2
  | .i_s2 => s₂ ^ 2
  | .i_s4 => s₄ ^ 2
  | .i_s6 => s₆ ^ 2
  | .i_s8 => s₈ ^ 2
  | .i_s3 => s₃ ^ 4
  | .i_s5 => s₅ ^ 4
  | .i_s7 => s₇ ^ 4
  -- (II)
  | .ii_s1_s2 => parrottCommutator s₁ s₂
  | .ii_s1_s3 => parrottCommutator s₁ s₃
  | .ii_s1_s5 => parrottCommutator s₁ s₅
  -- (III)
  | .iii_s1_s6 => parrottCommutator s₁ s₆ * parrottR3⁻¹
  | .iii_s1_s7 => parrottCommutator s₁ s₇ * (s₂ * parrottR3 * parrottR5)⁻¹
  | .iii_s1_s8 => parrottCommutator s₁ s₈ * (s₇ ^ 2 * parrottR3 * s₁)⁻¹
  -- (IV)
  | .iv_s2_s4 => parrottCommutator s₂ s₄
  | .iv_s2_s6 => parrottCommutator s₂ s₆
  | .iv_s2_s8 => parrottCommutator s₂ s₈ * (s₄ * s₆)⁻¹
  | .iv_s7_s2 => parrottCommutator s₇ s₂ * (s₄ * parrottR5)⁻¹
  -- (V)
  | .v_s7_s4 => parrottCommutator s₇ s₄ * (parrottR3 * parrottR5)⁻¹
  | .v_s3_s5 => parrottCommutator s₃ s₅ * (s₂ * parrottR3 * s₄)⁻¹
  | .v_s5_s4 => parrottCommutator s₅ s₄ * parrottR3⁻¹
  -- (VI)
  | .vi_r1_r8 => (r₁ * r₈) ^ 8
  | .vi_s1_r1 => (s₁ * r₁) ^ 5
  | .vi_r8_s8 => (r₈ * s₈) ^ 3
  -- (VII)
  | .vii_s2 => r₁ * s₂ * r₁ * s₈⁻¹
  | .vii_s4 => r₁ * s₄ * r₁ * s₆⁻¹
  | .vii_s5 => r₁ * s₅ * r₁ * ((s₁ * r₁) ^ 2 * s₅)⁻¹
  | .vii_s3 => r₁ * s₃ * r₁ * ((s₁ * r₁) ^ 2 * parrottR7)⁻¹
  | .vii_r3 => r₁ * parrottR3 * r₁ * (s₇ * parrottR7)⁻¹
  -- (VIII)
  | .viii_s2 => r₈ * s₂ * r₈ * s₆⁻¹
  | .viii_s4 => r₈ * s₄ * r₈ * s₄⁻¹
  | .viii_s1 => r₈ * s₁ * r₈ * (s₇ * parrottR7)⁻¹
  | .viii_s7 => r₈ * s₇ * r₈ * (s₇⁻¹)⁻¹
  | .viii_s3 => r₈ * s₃ * r₈ * (s₇ * s₅)⁻¹
  | .viii_r3 => r₈ * parrottR3 * r₈ * parrottR5⁻¹

/-- The set of defining relators of Parrott's presentation. -/
@[expose] public def parrottRelatorSet : Set (FreeGroup ParrottGenerator) :=
  Set.range parrottRelator

/-- The concrete group defined by Parrott's ten-generator presentation. -/
@[expose] public def ParrottGroup := PresentedGroup parrottRelatorSet
  deriving Group

/-- The canonical generators in Parrott's presented group. -/
@[expose] public def parrottGenerator (a : ParrottGenerator) : ParrottGroup :=
  PresentedGroup.of a

/-- An assignment satisfies all 37 defining relators exactly. -/
@[expose] public def SatisfiesParrottRelations {G : Type*} [Group G]
    (g : ParrottGenerator → G) : Prop :=
  ∀ i : ParrottRelatorIndex, FreeGroup.lift g (parrottRelator i) = 1

/-- The homomorphism induced by an assignment satisfying Parrott's relators. -/
public def parrottLift {G : Type*} [Group G] (g : ParrottGenerator → G)
    (h : SatisfiesParrottRelations g) : ParrottGroup →* G :=
  PresentedGroup.toGroup (by
    rintro _ ⟨i, rfl⟩
    exact h i)

/-- The induced homomorphism takes each generator to its assigned image. -/
@[simp] public theorem parrottLift_generator {G : Type*} [Group G]
    (g : ParrottGenerator → G) (h : SatisfiesParrottRelations g)
    (a : ParrottGenerator) : parrottLift g h (parrottGenerator a) = g a :=
  PresentedGroup.toGroup.of _

/-- Assignments satisfying the 37 relators extend uniquely to the model. -/
public theorem exists_unique_parrott_lift {G : Type*} [Group G]
    (g : ParrottGenerator → G) (h : SatisfiesParrottRelations g) :
    ∃! φ : ParrottGroup →* G, ∀ a, φ (parrottGenerator a) = g a := by
  refine ⟨parrottLift g h, fun a => parrottLift_generator g h a, ?_⟩
  intro φ hφ
  apply PresentedGroup.ext
  intro a
  exact (hφ a).trans (parrottLift_generator g h a).symm

/-- The canonical generators satisfy every defining relator. -/
public theorem parrott_generators_satisfy_relations :
    SatisfiesParrottRelations parrottGenerator := by
  have hlift : FreeGroup.lift parrottGenerator = PresentedGroup.mk parrottRelatorSet := by
    ext a
    rfl
  intro i
  rw [hlift]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

end Tits
