module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Streaming

/-!
# Bounded arithmetic samples on the literal HS matrices

The numerical certificate below is checked in Lean and connected to the
actual packed matrix product. It is a representative arithmetic check and
does not establish any whole-matrix relator.

Generated from the retained, hash-checked HSG1-f4r896aB0 data by
`source/GenerateSample.py`. ATLAS attribution and conventions are preserved
in `TracePair/source/README.md`. See `source/README.md` for measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Sample
open Certificates Streaming

private def lastInput : Packed.Row := (236511543024720656684649746200291874814349831256478902982857562689542437630791322308699003022887740885316140741531650517112901629018539119961766571912857120857919174011720070469320108031869540512338711394481766571756366578854490995154837057618194317695902848732299517347, 294545475279803267828137783934002205613645623862364142761431501017117319523504664550529823471528657933309147054811868768288972384714412355804514050161400389117046775037909554007985825668732845967862954703335407477169010673146282855685755951529647494543785000958209132439)

def abLastRow : Packed.Row := (497101262948547864945708853944464939285441613550120247172603367117392739129826848028814312383198951932576288063705581979467857723435523472333641022339832122047392638249752132719667518484753818299025488727022992953620468217687657472095799716746394844724151891109302219314, 400607480642380404496129289697161881890837130072617667920352441716079835769767620481247033203365513434554781460548515773052488944375229284643597821089113482004431848712320775390720244911175235882665442864784953705400139705407044800129074966290828015148737742658425414917)

set_option maxRecDepth 4096 in
private theorem source_row_checked :
    generatorRowsA.getD 895 (0, 0) = lastInput := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem last_product_checked :
    product lastInput generatorRowsB = abLastRow := by
  decide +kernel

/-- A complete row of the literal packed matrix product, not a scalar test. -/
theorem matrix_product_last_row :
    (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB) (895 : Fin 896) =
      vector abLastRow := by
  calc
    _ = Matrix.vecMul (vector (generatorRowsA.getD 895 (0, 0)))
        (Packed.eval 896 generatorRowsB) := rfl
    _ = vector (product (generatorRowsA.getD 895 (0, 0)) generatorRowsB) :=
      (vector_product _ generatorRowsB generatorRowsB_length).symm
    _ = vector abLastRow := by rw [source_row_checked, last_product_checked]


end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Sample
