module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Reduction

/-!
# Candidate local words for the two-part certificate

These are the unchanged register computations of the ATLAS programs
`BG1-max2W1` and `BG1-max4W1`, interpreted in any group. The source programs
and provenance are in `../source/README.md`. A new binding is used for each
register write, preserving the multiplication order and inverse convention.

Evaluating inside `standardImage` proves membership without any matrix
calculation. No local subgroup shape, order, or identification is asserted.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.TwoPart

variable {G : Type*} [Group G]

/-- The final registers 1 and 2 of `BG1-max2W1`. -/
def max2Words (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 * b
  let r5 := r3 * r3
  let r3 := r5 * r5
  let r2 := r3 * r4
  let r3 := r2 * r2
  let r4 := r2 * r3
  let r5 := r4 * r4
  let r3 := r5 * r5
  let r4 := r3 * r3
  let r3 := a * r4
  let r1 := r3 * r3
  (r1, r2)

/-- The final registers 1 and 2 of `BG1-max4W1`. -/
def max4Words (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 * b
  let r5 := r3 * r4
  let r6 := r3 * r5
  let r7 := r6 ^ 10
  let r8 := r3 * r7
  let r9 := r8⁻¹
  let r8 := r7 * r3
  let r10 := r9 * r8
  let r11 := r10 ^ 17
  let r2 := r3 * r11
  let r8 := r4 * r7
  let r9 := r8⁻¹
  let r8 := r7 * r4
  let r10 := r9 * r8
  let r11 := r10 ^ 16
  let r12 := r4 * r11
  let r10 := r2 * r12
  let r9 := r10 ^ 20
  let r8 := r7 * r9
  let r9 := r3 * r8
  let r10 := r9⁻¹
  let r9 := r8 * r3
  let r8 := r10 * r9
  let r1 := r8 ^ 12
  (r1, r2)

/-- The first fixed generator, regarded as an element of its generated subgroup. -/
def a (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) : standardImage ha hb :=
  ⟨standardA ha, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- The second fixed generator, regarded as an element of its generated subgroup. -/
def b (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) : standardImage ha hb :=
  ⟨standardB hb, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- Membership-certified outputs of the first candidate program. -/
def max2 (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    standardImage ha hb × standardImage ha hb := max2Words (a ha hb) (b ha hb)

/-- Membership-certified outputs of the second candidate program. -/
def max4 (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    standardImage ha hb × standardImage ha hb := max4Words (a ha hb) (b ha hb)

end BabyMonster.OrderLowerBound.TwoPart
