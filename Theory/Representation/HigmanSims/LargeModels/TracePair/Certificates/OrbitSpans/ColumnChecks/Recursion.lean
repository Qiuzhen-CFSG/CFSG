module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Transpose
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block03
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block05
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block07
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block08
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block09
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block10
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block11
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block12
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block13
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block14
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion.Block15

/-!
# The complete literal HS column recursion

All 895 products use the saved parent and letter arrays. The proved transpose
interpretations convert these row products into the required column action.
Source: `Certificates/source/witnesses.json.gz`; see `ColumnChecks/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks

theorem recursion_all : checkRange (recursionStep transposedRowsA transposedRowsB) 0 895 = true :=
  checkRange_add (recursionStep transposedRowsA transposedRowsB) 0 448 447
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 0 224 224
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 0 112 112
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 0 56 56
    (recursionBlock00)
    (recursionBlock01))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 112 56 56
    (recursionBlock02)
    (recursionBlock03)))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 224 112 112
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 224 56 56
    (recursionBlock04)
    (recursionBlock05))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 336 56 56
    (recursionBlock06)
    (recursionBlock07))))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 448 224 223
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 448 112 112
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 448 56 56
    (recursionBlock08)
    (recursionBlock09))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 560 56 56
    (recursionBlock10)
    (recursionBlock11)))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 672 112 111
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 672 56 56
    (recursionBlock12)
    (recursionBlock13))
    (checkRange_add (recursionStep transposedRowsA transposedRowsB) 784 56 55
    (recursionBlock14)
    (recursionBlock15))))

theorem recursion_checked : ColumnRecursion :=
  recursion_of_check transposedRowsA transposedRowsB transposedRowsA_length transposedRowsB_length
    transposedRowsA_eq transposedRowsB_eq recursion_all

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
