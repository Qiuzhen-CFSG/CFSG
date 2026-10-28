module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.TwoPart.WordWitnesses.Evaluation

/-!
# Word syntax for the preserved local subgroup programs

These expressions transcribe the register writes of `BG1-max2W1` and `BG1-max4W1`.
The evaluation theorems identify them with `TwoPart.max2` and `TwoPart.max4`,
without making any subgroup identification. Source attribution and hashes are in
`ImageSize/source/README.md`. The words are inputs for a search for a polycyclic
sequence, not such a sequence themselves.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.TwoPart.WordWitnesses

/-- The unchanged ATLAS `max2` register program as word expressions. -/
def max2Program : Word × Word :=
  let r1 : Word := .a
  let r2 : Word := .b
  let r3 := .mul r1 r2
  let r4 := .mul r3 r2
  let r5 := .mul r3 r3
  let r3 := .mul r5 r5
  let r2 := .mul r3 r4
  let r3 := .mul r2 r2
  let r4 := .mul r2 r3
  let r5 := .mul r4 r4
  let r3 := .mul r5 r5
  let r4 := .mul r3 r3
  let r3 := .mul r1 r4
  let r1 := .mul r3 r3
  (r1, r2)

theorem max2Program_eval {G : Type*} [Group G] (a b : G) :
    ((max2Program.1).eval a b, (max2Program.2).eval a b) = max2Words a b := rfl

theorem max2Program_element (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    ((max2Program.1).element ha hb, (max2Program.2).element ha hb) = max2 ha hb := rfl

/-- The unchanged ATLAS `max4` register program as word expressions. -/
def max4Program : Word × Word :=
  let r1 : Word := .a
  let r2 : Word := .b
  let r3 := .mul r1 r2
  let r4 := .mul r3 r2
  let r5 := .mul r3 r4
  let r6 := .mul r3 r5
  let r7 := .pow r6 10
  let r8 := .mul r3 r7
  let r9 := .inv r8
  let r8 := .mul r7 r3
  let r10 := .mul r9 r8
  let r11 := .pow r10 17
  let r2 := .mul r3 r11
  let r8 := .mul r4 r7
  let r9 := .inv r8
  let r8 := .mul r7 r4
  let r10 := .mul r9 r8
  let r11 := .pow r10 16
  let r12 := .mul r4 r11
  let r10 := .mul r2 r12
  let r9 := .pow r10 20
  let r8 := .mul r7 r9
  let r9 := .mul r3 r8
  let r10 := .inv r9
  let r9 := .mul r8 r3
  let r8 := .mul r10 r9
  let r1 := .pow r8 12
  (r1, r2)

theorem max4Program_eval {G : Type*} [Group G] (a b : G) :
    ((max4Program.1).eval a b, (max4Program.2).eval a b) = max4Words a b := rfl

theorem max4Program_element (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    ((max4Program.1).element ha hb, (max4Program.2).element ha hb) = max4 ha hb := rfl

end BabyMonster.OrderLowerBound.TwoPart.WordWitnesses
