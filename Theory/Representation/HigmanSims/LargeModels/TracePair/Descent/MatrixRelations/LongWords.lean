module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Circuit
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.LastTwo

/-!
# The six literal long HS matrix relations

The exact monoid circuit is connected to the fixed packed matrices through 46
concrete multiplication gates, certified by the four independent numerical
batches imported above. Substitution in the circuit proves every positive
relation at indices 7--12, including R1--R3, without extra hypotheses.

Source: the retained ATLAS HSG1-P1.M and HSG1-f4r896aB0 matrices; see
`LongWords/source/README.md` for the exact words and arithmetic conventions.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
open Certificates

private theorem long_index (i : Fin 13) (hi : 7 ≤ i.val) :
    i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega

/-- Substitute all numerical products into the exact ordered monoid circuit. -/
theorem relations_of_products (h : ∀ i : Fin 46, ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 := by
  let A := Packed.eval 896 generatorRowsA
  let B := Packed.eval 896 generatorRowsB
  have h00 : word00 A B = candidate 0 := rfl
  have h01 : word01 A B = candidate 1 := rfl
  have h02 : word02 A B = candidate 2 :=
    (congrArg₂ (· * ·) h01 h01).trans (h 0)
  have h03 : word03 A B = candidate 3 :=
    (congrArg₂ (· * ·) h00 h02).trans (h 1)
  have h04 : word04 A B = candidate 4 :=
    (congrArg₂ (· * ·) h00 h01).trans (h 2)
  have h05 : word05 A B = candidate 5 :=
    (congrArg₂ (· * ·) h04 h03).trans (h 3)
  have h06 : word06 A B = candidate 6 :=
    (congrArg₂ (· * ·) h04 h05).trans (h 4)
  have h07 : word07 A B = candidate 7 :=
    (congrArg₂ (· * ·) h03 h01).trans (h 5)
  have h08 : word08 A B = candidate 8 :=
    (congrArg₂ (· * ·) h03 h02).trans (h 6)
  have h09 : word09 A B = candidate 9 :=
    (congrArg₂ (· * ·) h06 h08).trans (h 7)
  have h10 : word10 A B = candidate 10 :=
    (congrArg₂ (· * ·) h07 h07).trans (h 8)
  have h11 : word11 A B = candidate 11 :=
    (congrArg₂ (· * ·) h06 h02).trans (h 9)
  have h12 : word12 A B = candidate 12 :=
    (congrArg₂ (· * ·) h09 h07).trans (h 10)
  have h13 : word13 A B = candidate 13 :=
    (congrArg₂ (· * ·) h08 h03).trans (h 11)
  have h14 : word14 A B = candidate 14 :=
    (congrArg₂ (· * ·) h06 h01).trans (h 12)
  have h15 : word15 A B = candidate 15 :=
    (congrArg₂ (· * ·) h10 h03).trans (h 13)
  have h16 : word16 A B = candidate 16 :=
    (congrArg₂ (· * ·) h06 h03).trans (h 14)
  have h17 : word17 A B = candidate 17 :=
    (congrArg₂ (· * ·) h05 h02).trans (h 15)
  have h18 : word18 A B = candidate 18 :=
    (congrArg₂ (· * ·) h12 h11).trans (h 16)
  have h19 : word19 A B = candidate 19 :=
    (congrArg₂ (· * ·) h12 h13).trans (h 17)
  have h20 : word20 A B = candidate 20 :=
    (congrArg₂ (· * ·) h14 h10).trans (h 18)
  have h21 : word21 A B = candidate 21 :=
    (congrArg₂ (· * ·) h19 h20).trans (h 19)
  have h22 : word22 A B = candidate 22 :=
    (congrArg₂ (· * ·) h21 h07).trans (h 20)
  have h23 : word23 A B = candidate 23 :=
    (congrArg₂ (· * ·) h05 h15).trans (h 21)
  have h24 : word24 A B = candidate 24 :=
    (congrArg₂ (· * ·) h15 h05).trans (h 22)
  have h25 : word25 A B = candidate 25 :=
    (congrArg₂ (· * ·) h13 h13).trans (h 23)
  have h26 : word26 A B = candidate 26 :=
    (congrArg₂ (· * ·) h23 h24).trans (h 24)
  have h27 : word27 A B = candidate 27 :=
    (congrArg₂ (· * ·) h26 h25).trans (h 25)
  have h28 : word28 A B = candidate 28 :=
    (congrArg₂ (· * ·) h16 h17).trans (h 26)
  have h29 : word29 A B = candidate 29 :=
    (congrArg₂ (· * ·) h08 h05).trans (h 27)
  have h30 : word30 A B = candidate 30 :=
    (congrArg₂ (· * ·) h03 h14).trans (h 28)
  have h31 : word31 A B = candidate 31 :=
    (congrArg₂ (· * ·) h08 h07).trans (h 29)
  have h32 : word32 A B = candidate 32 :=
    (congrArg₂ (· * ·) h28 h29).trans (h 30)
  have h33 : word33 A B = candidate 33 :=
    (congrArg₂ (· * ·) h30 h31).trans (h 31)
  have h34 : word34 A B = candidate 34 :=
    (congrArg₂ (· * ·) h32 h33).trans (h 32)
  have h35 : word35 A B = candidate 35 :=
    (congrArg₂ (· * ·) h18 h18).trans (h 33)
  have h36 : word36 A B = candidate 36 :=
    (congrArg₂ (· * ·) h06 h06).trans (h 34)
  have h37 : word37 A B = candidate 37 :=
    (congrArg₂ (· * ·) h11 h16).trans (h 35)
  have h38 : word38 A B = candidate 38 :=
    (congrArg₂ (· * ·) h03 h11).trans (h 36)
  have h39 : word39 A B = candidate 39 :=
    (congrArg₂ (· * ·) h36 h37).trans (h 37)
  have h40 : word40 A B = candidate 40 :=
    (congrArg₂ (· * ·) h39 h38).trans (h 38)
  have h41 : word41 A B = candidate 41 :=
    (congrArg₂ (· * ·) h06 h05).trans (h 39)
  have h42 : word42 A B = candidate 42 :=
    (congrArg₂ (· * ·) h05 h09).trans (h 40)
  have h43 : word43 A B = candidate 43 :=
    (congrArg₂ (· * ·) h05 h01).trans (h 41)
  have h44 : word44 A B = candidate 44 :=
    (congrArg₂ (· * ·) h17 h03).trans (h 42)
  have h45 : word45 A B = candidate 45 :=
    (congrArg₂ (· * ·) h41 h42).trans (h 43)
  have h46 : word46 A B = candidate 46 :=
    (congrArg₂ (· * ·) h43 h44).trans (h 44)
  have h47 : word47 A B = candidate 47 :=
    (congrArg₂ (· * ·) h45 h46).trans (h 45)
  intro i hi
  rcases long_index i hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (relation_7 A B).trans (h22.trans identityRows_eval)
  · exact (relation_8 A B).trans (h27.trans identityRows_eval)
  · exact (relation_9 A B).trans (h34.trans identityRows_eval)
  · exact (relation_10 A B).trans (h35.trans identityRows_eval)
  · exact (relation_11 A B).trans (h40.trans identityRows_eval)
  · exact (relation_12 A B).trans (h47.trans identityRows_eval)

/-- Assemble independent numerical gate batches, with no ordering dependency
between their fixed-matrix checks. -/
theorem relations_of_batches
    (hshared : ∀ i : Fin 46, i.val < 17 → ProductCheck i)
    (hfirst : ∀ i : Fin 46, 17 ≤ i.val → i.val < 26 → ProductCheck i)
    (hmiddle : ∀ i : Fin 46, 26 ≤ i.val → i.val < 34 → ProductCheck i)
    (hlast : ∀ i : Fin 46, 34 ≤ i.val → ProductCheck i) :
    ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
      (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 := by
  apply relations_of_products
  intro i
  by_cases h₁ : i.val < 17
  · exact hshared i h₁
  by_cases h₂ : i.val < 26
  · exact hfirst i (by omega) h₂
  by_cases h₃ : i.val < 34
  · exact hmiddle i (by omega) h₃
  exact hlast i (by omega)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates

/-- All six long literal positive relations on the exact packed degree-896
matrices, including the three additional source relators R1--R3. -/
theorem long_relations : ∀ i : Fin 13, 7 ≤ i.val → positiveRelation
    (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) i = 1 :=
  LongWords.relations_of_batches LongWords.shared_products LongWords.first_products
    LongWords.middle_products LongWords.last_products

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
