module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block00
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block01
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block02
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block03
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block04
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block05
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block06
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse.Block07

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks

theorem inverse_all : checkRange inverseStep 0 896 = true :=
  checkRange_add (inverseStep) 0 448 448
    (checkRange_add (inverseStep) 0 224 224
    (checkRange_add (inverseStep) 0 112 112
    (inverseBlock00)
    (inverseBlock01))
    (checkRange_add (inverseStep) 224 112 112
    (inverseBlock02)
    (inverseBlock03)))
    (checkRange_add (inverseStep) 448 224 224
    (checkRange_add (inverseStep) 448 112 112
    (inverseBlock04)
    (inverseBlock05))
    (checkRange_add (inverseStep) 672 112 112
    (inverseBlock06)
    (inverseBlock07)))

theorem inverse_checked : columnInverse * columnMatrix = 1 := inverse_of_check inverse_all

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks
