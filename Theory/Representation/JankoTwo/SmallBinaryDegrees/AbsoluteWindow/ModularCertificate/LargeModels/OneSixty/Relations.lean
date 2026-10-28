module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
/-!
# The five degree-160 ATLAS relators

Packed multiplication certificates verify the five words using addition chains.
The resulting units use A as its own inverse and B squared as the inverse of B,
matching the exact ATLAS presentation conventions. Original data and attribution:
`../source/README.md`. Generated witnesses are never proof premises.
-/
@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
open Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization
open Data
private theorem relatorChecks :
    checkProduct 160 a a a2 = true ∧
    checkProduct 160 b b b2 = true ∧
    checkProduct 160 b b2 b3 = true ∧
    checkProduct 160 a b ab = true ∧
    checkProduct 160 ab ab ab2 = true ∧
    checkProduct 160 ab2 ab ab3 = true ∧
    checkProduct 160 ab2 ab2 ab4 = true ∧
    checkProduct 160 ab3 ab4 ab7 = true ∧
    checkProduct 160 a b2 u = true ∧
    checkProduct 160 u ab comm = true ∧
    checkProduct 160 comm comm comm2 = true ∧
    checkProduct 160 comm2 comm2 comm4 = true ∧
    checkProduct 160 comm4 comm2 comm6 = true ∧
    checkProduct 160 comm6 comm6 comm12 = true ∧
    checkProduct 160 ab2 u long1 = true ∧
    checkProduct 160 long1 ab long2 = true ∧
    checkProduct 160 long2 u long = true ∧
    checkProduct 160 long long longSq = true ∧
    checkProduct 160 longSq long longCube = true ∧
    checkProduct 160 longCube longCube long6 = true :=
  ⟨Checks.a2_check, Checks.b2_check, Checks.b3_check, Checks.ab_check, Checks.ab2_check, Checks.ab3_check, Checks.ab4_check, Checks.ab7_check, Checks.u_check, Checks.comm_check, Checks.comm2_check, Checks.comm4_check, Checks.comm6_check, Checks.comm12_check, Checks.long1_check, Checks.long2_check, Checks.long_check, Checks.longSq_check, Checks.longCube_check, Checks.long6_check⟩

variable (F : Type*) [Field F] [CharP F 2]

def matrixA : Matrix (Fin 160) (Fin 160) F := Binary.eval F 160 a
def matrixB : Matrix (Fin 160) (Fin 160) F := Binary.eval F 160 b

def MatrixRelations (A B : Matrix (Fin 160) (Fin 160) F) : Prop :=
  A ^ 2 = 1 ∧ B ^ 3 = 1 ∧ (A * B) ^ 7 = 1 ∧
    (A * B ^ 2 * A * B) ^ 12 = 1 ∧
    (A * B * A * B * A * B ^ 2 * A * B * A * B ^ 2) ^ 6 = 1

theorem matrix_relations : MatrixRelations F (matrixA F) (matrixB F) := by
  obtain ⟨c_a2, c_b2, c_b3, c_ab, c_ab2, c_ab3, c_ab4, c_ab7, c_u, c_comm, c_comm2, c_comm4, c_comm6, c_comm12, c_long1, c_long2, c_long, c_longSq, c_longCube, c_long6⟩ := relatorChecks
  have h_a2 := Binary.eval_product F 160 a a a2 (product_sound 160 _ _ _ c_a2)
  have h_b2 := Binary.eval_product F 160 b b b2 (product_sound 160 _ _ _ c_b2)
  have h_b3 := Binary.eval_product F 160 b b2 b3 (product_sound 160 _ _ _ c_b3)
  have h_ab := Binary.eval_product F 160 a b ab (product_sound 160 _ _ _ c_ab)
  have h_ab2 := Binary.eval_product F 160 ab ab ab2 (product_sound 160 _ _ _ c_ab2)
  have h_ab3 := Binary.eval_product F 160 ab2 ab ab3 (product_sound 160 _ _ _ c_ab3)
  have h_ab4 := Binary.eval_product F 160 ab2 ab2 ab4 (product_sound 160 _ _ _ c_ab4)
  have h_ab7 := Binary.eval_product F 160 ab3 ab4 ab7 (product_sound 160 _ _ _ c_ab7)
  have h_u := Binary.eval_product F 160 a b2 u (product_sound 160 _ _ _ c_u)
  have h_comm := Binary.eval_product F 160 u ab comm (product_sound 160 _ _ _ c_comm)
  have h_comm2 := Binary.eval_product F 160 comm comm comm2 (product_sound 160 _ _ _ c_comm2)
  have h_comm4 := Binary.eval_product F 160 comm2 comm2 comm4 (product_sound 160 _ _ _ c_comm4)
  have h_comm6 := Binary.eval_product F 160 comm4 comm2 comm6 (product_sound 160 _ _ _ c_comm6)
  have h_comm12 := Binary.eval_product F 160 comm6 comm6 comm12 (product_sound 160 _ _ _ c_comm12)
  have h_long1 := Binary.eval_product F 160 ab2 u long1 (product_sound 160 _ _ _ c_long1)
  have h_long2 := Binary.eval_product F 160 long1 ab long2 (product_sound 160 _ _ _ c_long2)
  have h_long := Binary.eval_product F 160 long2 u long (product_sound 160 _ _ _ c_long)
  have h_longSq := Binary.eval_product F 160 long long longSq (product_sound 160 _ _ _ c_longSq)
  have h_longCube := Binary.eval_product F 160 longSq long longCube (product_sound 160 _ _ _ c_longCube)
  have h_long6 := Binary.eval_product F 160 longCube longCube long6 (product_sound 160 _ _ _ c_long6)
  have hi : Binary.eval F 160 identity = 1 := one_sound F 160 identity Checks.identity_check
  change MatrixRelations F (Binary.eval F 160 a) (Binary.eval F 160 b)
  let A := Binary.eval F 160 a
  let B := Binary.eval F 160 b
  have ha : A ^ 2 = 1 := by
    change (Binary.eval F 160 a) ^ 2 = 1
    rw [pow_two, h_a2]
    exact hi
  have hb : B ^ 3 = 1 := by
    change (Binary.eval F 160 b) ^ 3 = 1
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, pow_two, h_b2, h_b3]
    exact hi
  have hab : (A * B) ^ 7 = 1 := by
    calc
      _ = ((A * B) * (A * B) * (A * B)) *
          (((A * B) * (A * B)) * ((A * B) * (A * B))) := by noncomm_ring
      _ = 1 := by
        dsimp [A, B]
        simp only [h_ab, h_ab2, h_ab3, h_ab4, h_ab7]
        exact hi
  have hc : A * B ^ 2 * A * B = Binary.eval F 160 comm := by
    calc
      _ = (A * (B * B)) * (A * B) := by noncomm_ring
      _ = _ := by dsimp [A, B]; rw [h_b2, h_u, h_ab, h_comm]
  have hc12 : (A * B ^ 2 * A * B) ^ 12 = 1 := by
    rw [hc]
    calc
      _ = (((Binary.eval F 160 comm) ^ 2) ^ 2 * (Binary.eval F 160 comm) ^ 2) ^ 2 := by noncomm_ring
      _ = 1 := by
        simp only [pow_two, h_comm2, h_comm4, h_comm6, h_comm12]
        exact hi
  have hl : A * B * A * B * A * B ^ 2 * A * B * A * B ^ 2 =
      Binary.eval F 160 long := by
    calc
      _ = ((A * B) * (A * B)) * (A * (B * B)) * (A * B) * (A * (B * B)) := by noncomm_ring
      _ = _ := by
        dsimp [A, B]
        simp only [h_ab, h_ab2, h_b2, h_u, h_long1, h_long2, h_long]
  have hl6 : (A * B * A * B * A * B ^ 2 * A * B * A * B ^ 2) ^ 6 = 1 := by
    rw [hl]
    calc
      _ = ((Binary.eval F 160 long) ^ 2 * Binary.eval F 160 long) ^ 2 := by noncomm_ring
      _ = 1 := by
        simp only [pow_two, h_longSq, h_longCube, h_long6]
        exact hi
  exact ⟨ha, hb, hab, hc12, hl6⟩

def unitA : (Matrix (Fin 160) (Fin 160) F)ˣ :=
  ⟨matrixA F, matrixA F, by simpa only [pow_two] using (matrix_relations F).1,
    by simpa only [pow_two] using (matrix_relations F).1⟩

def unitB : (Matrix (Fin 160) (Fin 160) F)ˣ :=
  ⟨matrixB F, matrixB F ^ 2,
    by simpa only [← pow_succ'] using (matrix_relations F).2.1,
    by simpa only [← pow_succ] using (matrix_relations F).2.1⟩

theorem units_relations : Presentation.Relations (unitA F) (unitB F) := by
  intro i
  apply Units.ext
  fin_cases i
  · exact (matrix_relations F).1
  · exact (matrix_relations F).2.1
  · exact (matrix_relations F).2.2.1
  · exact (matrix_relations F).2.2.2.1
  · exact (matrix_relations F).2.2.2.2

/-- The intermediate word used in the literal algebra element. -/
theorem u_identity (F : Type*) [Field F] [CharP F 2] :
    matrixA F * matrixB F ^ 2 = Binary.eval F 160 u := by
  have hb2 := Binary.eval_product F 160 b b b2
    (product_sound 160 _ _ _ relatorChecks.2.1)
  have hu := Binary.eval_product F 160 a b2 u
    (product_sound 160 _ _ _ relatorChecks.2.2.2.2.2.2.2.2.1)
  change Binary.eval F 160 a * Binary.eval F 160 b ^ 2 = _
  rw [pow_two, hb2, hu]
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
