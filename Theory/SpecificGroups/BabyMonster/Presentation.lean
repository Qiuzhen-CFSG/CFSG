module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# The eleven-generator presentation of the Baby Monster

This module defines a fixed group by the `Y₄₃₃` presentation in
T. Breuer, K. Magaard and R. A. Wilson, *Verification of the ordinary character
 table of the Baby Monster*, J. Algebra 534 (2019), §3.1,
https://arxiv.org/abs/1902.07758. The generators here are indexed from zero:
`generator i` denotes the source's `t_(i+1)`.

The construction is the free group on eleven letters modulo the normal closure
of the Coxeter relators, the spider relator, and both ninth-power relators.
The defining equations and universal property follow from this quotient.
This module does not assert finiteness, order, or simplicity: these require
separate proofs about this particular presentation. In particular, no existence
or classification assertion is used to define the carrier.
-/

@[expose] public section

namespace BabyMonster

/-- Vertices of the `Y₄₃₃` diagram, with zero-based indices. -/
abbrev Generator := Fin 11

/-- Edges oriented by increasing index, as listed in §3.1 of the source. -/
def edges : List (Generator × Generator) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7),
    (4, 8), (8, 9), (9, 10)]

/-- The Coxeter exponent for an increasing pair of distinct vertices. -/
def coxeterExponent (i j : Generator) : ℕ :=
  if (i, j) ∈ edges then 3 else 2

/-- The nine-letter spider word, before taking its tenth power. -/
def spiderWord {G : Type*} [Monoid G] (t : Generator → G) : G :=
  t 4 * t 3 * t 2 * t 4 * t 5 * t 6 * t 4 * t 8 * t 9

/-- The first seven-letter word whose ninth power kills part of the centre. -/
def firstArmWord {G : Type*} [Monoid G] (t : Generator → G) : G :=
  t 4 * t 3 * t 2 * t 5 * t 6 * t 7 * t 8

/-- The second seven-letter word whose ninth power kills the remaining centre. -/
def secondArmWord {G : Type*} [Monoid G] (t : Generator → G) : G :=
  t 4 * t 3 * t 2 * t 5 * t 8 * t 9 * t 10

/-- Exactly the relators of the presentation for the simple group, including
both relations needed to pass from the central extension to the Baby Monster. -/
inductive Relator : FreeGroup Generator → Prop
  | square (i : Generator) : Relator (FreeGroup.of i ^ 2)
  | pair (i j : Generator) (h : i < j) :
      Relator ((FreeGroup.of i * FreeGroup.of j) ^ coxeterExponent i j)
  | spider : Relator (spiderWord FreeGroup.of ^ 10)
  | firstArm : Relator (firstArmWord FreeGroup.of ^ 9)
  | secondArm : Relator (secondArmWord FreeGroup.of ^ 9)

/-- The fixed, intrinsically presented carrier. -/
abbrev Carrier := PresentedGroup {w | Relator w}

/-- The canonical eleven generators of the quotient. -/
def generator (i : Generator) : Carrier := PresentedGroup.of i

/-- Every generator is an involution or the identity. -/
theorem generator_sq (i : Generator) : generator i ^ 2 = 1 := by
  simpa only [map_pow, generator, PresentedGroup.of] using
    (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.square i))

/-- The Coxeter relations of the diagram. -/
theorem generator_pair (i j : Generator) (h : i < j) :
    (generator i * generator j) ^ coxeterExponent i j = 1 := by
  simpa only [map_pow, map_mul, generator, PresentedGroup.of] using
    (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.pair i j h))

/-- The spider relation. -/
theorem generator_spider : spiderWord generator ^ 10 = 1 := by
  simpa only [spiderWord, map_pow, map_mul, generator, PresentedGroup.of] using
    (PresentedGroup.one_of_mem (rels := {w | Relator w}) Relator.spider)

/-- The first additional ninth-power relation. -/
theorem generator_firstArm : firstArmWord generator ^ 9 = 1 := by
  simpa only [firstArmWord, map_pow, map_mul, generator, PresentedGroup.of] using
    (PresentedGroup.one_of_mem (rels := {w | Relator w}) Relator.firstArm)

/-- The second additional ninth-power relation. -/
theorem generator_secondArm : secondArmWord generator ^ 9 = 1 := by
  simpa only [secondArmWord, map_pow, map_mul, generator, PresentedGroup.of] using
    (PresentedGroup.one_of_mem (rels := {w | Relator w}) Relator.secondArm)

/-- The canonical generators generate the entire presented group. -/
theorem closure_range_generator : Subgroup.closure (Set.range generator) = ⊤ :=
  PresentedGroup.closure_range_of _

/-- The explicit equations required to map the presented group to another group.
This is a universal-property interface, not an existence certificate. -/
structure Relations {G : Type*} [Group G] (t : Generator → G) : Prop where
  square : ∀ i, t i ^ 2 = 1
  pair : ∀ i j, i < j → (t i * t j) ^ coxeterExponent i j = 1
  spider : spiderWord t ^ 10 = 1
  firstArm : firstArmWord t ^ 9 = 1
  secondArm : secondArmWord t ^ 9 = 1

/-- The quotient satisfies every equation of the presentation. -/
theorem generator_relations : Relations generator :=
  ⟨generator_sq, generator_pair, generator_spider, generator_firstArm, generator_secondArm⟩

/-- Evaluation sends each defining relator to the identity. -/
theorem Relations.eval_relator {G : Type*} [Group G] {t : Generator → G}
    (h : Relations t) {w : FreeGroup Generator} (hw : Relator w) :
    FreeGroup.lift t w = 1 := by
  cases hw with
  | square i => simpa using h.square i
  | pair i j hij => simpa using h.pair i j hij
  | spider => simpa [spiderWord] using h.spider
  | firstArm => simpa [firstArmWord] using h.firstArm
  | secondArm => simpa [secondArmWord] using h.secondArm

/-- A family satisfying the presentation induces a homomorphism from the fixed carrier. -/
def lift {G : Type*} [Group G] {t : Generator → G} (h : Relations t) : Carrier →* G :=
  PresentedGroup.toGroup (fun _ hw => h.eval_relator hw)

@[simp]
theorem lift_generator {G : Type*} [Group G] {t : Generator → G}
    (h : Relations t) (i : Generator) : lift h (generator i) = t i :=
  PresentedGroup.toGroup.of _

/-- A homomorphism out of the fixed carrier is determined by the eleven generators. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] {f g : Carrier →* G}
    (h : ∀ i, f (generator i) = g (generator i)) : f = g :=
  PresentedGroup.ext h

end BabyMonster
