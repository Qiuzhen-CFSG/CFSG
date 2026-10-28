module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Construction

/-!
# The signed trace-word convention

Letters ±1 and ±2 mean a,b or their inverses, in displayed product order.
For the units built from A²=1 and B³=1 their matrix values are A,A,B,B².
This bridge retains the original signed ATLAS trace word on the literal carrier.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Words

def signed {G : Type*} [Group G] (a b : G) (w : List ℤ) : G :=
  (w.map fun s => if s = 1 then a else if s = -1 then a⁻¹ else
    if s = 2 then b else b⁻¹).prod

theorem map_signed {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (w : List ℤ) : f (signed a b w) = signed (f a) (f b) w := by
  simp only [signed, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  dsimp only [Function.comp_def]
  split_ifs <;> simp only [map_inv]

def matrixWord {F : Type*} [Field F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (w : List ℤ) :=
  (w.map fun s => if s = 1 then A else if s = -1 then A else
    if s = 2 then B else B ^ 2).prod

theorem coe_signed_units {F : Type*} [Field F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (h : SmallModels.MatrixRelations A B) (w : List ℤ) :
    (signed (G := (Matrix (Fin n) (Fin n) F)ˣ)
      (SmallModels.unitA A B h) (SmallModels.unitB A B h) w :
      Matrix (Fin n) (Fin n) F) = matrixWord A B w := by
  change (Units.coeHom _) ((w.map _).prod) = _
  rw [map_list_prod]
  simp only [List.map_map, matrixWord]
  congr 1
  apply List.map_congr_left
  intro s _
  dsimp only [Function.comp_def]
  split_ifs <;> rfl

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Words
