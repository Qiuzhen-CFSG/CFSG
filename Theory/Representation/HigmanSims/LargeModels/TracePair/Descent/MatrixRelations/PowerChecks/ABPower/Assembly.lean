module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.ABProduct

/-!
# Assembly of the five remaining eleventh-power product checks

The unconditional `ABProduct.ab_eq_c` identifies the candidate C with the
literal product AB. This lemma connects the remaining numerical checks
C² = D, D² = E, CE = F, F² = G and GC = I to relator 2 of the unchanged
`Descent/source/HSG1-P1.M`. All five checks remain explicit until their
independent certificates have been supplied. No HS action is assumed.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower
open Certificates

/-- The particular five numerical checks sufficient for the exact source word. -/
theorem pow_eleven_eq_one_of_products
    (hCC : Packed.eval 896 cRows * Packed.eval 896 cRows = Packed.eval 896 dRows)
    (hDD : Packed.eval 896 dRows * Packed.eval 896 dRows = Packed.eval 896 eRows)
    (hCE : Packed.eval 896 cRows * Packed.eval 896 eRows = Packed.eval 896 fRows)
    (hFF : Packed.eval 896 fRows * Packed.eval 896 fRows = Packed.eval 896 gRows)
    (hGC : Packed.eval 896 gRows * Packed.eval 896 cRows = 1) :
    (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB) ^ 11 = 1 := by
  rw [ABProduct.ab_eq_c]
  have hd : Packed.eval 896 dRows = (Packed.eval 896 cRows) ^ 2 := by
    simpa only [pow_two] using hCC.symm
  have he : Packed.eval 896 eRows = (Packed.eval 896 cRows) ^ 4 := by
    calc
      Packed.eval 896 eRows = Packed.eval 896 dRows * Packed.eval 896 dRows := hDD.symm
      _ = (Packed.eval 896 cRows) ^ (2 + 2) := by rw [hd, ← pow_add]
  have hf : Packed.eval 896 fRows = (Packed.eval 896 cRows) ^ 5 := by
    calc
      Packed.eval 896 fRows = Packed.eval 896 cRows * Packed.eval 896 eRows := hCE.symm
      _ = (Packed.eval 896 cRows) ^ (4 + 1) := by rw [he, ← pow_succ']
  have hg : Packed.eval 896 gRows = (Packed.eval 896 cRows) ^ 10 := by
    calc
      Packed.eval 896 gRows = Packed.eval 896 fRows * Packed.eval 896 fRows := hFF.symm
      _ = (Packed.eval 896 cRows) ^ (5 + 5) := by rw [hf, ← pow_add]
  calc
    (Packed.eval 896 cRows) ^ 11 =
        (Packed.eval 896 cRows) ^ 10 * Packed.eval 896 cRows := pow_succ _ 10
    _ = Packed.eval 896 gRows * Packed.eval 896 cRows := by rw [hg]
    _ = 1 := hGC

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower
