module

public import Theory.GroupTheory.TINormalizerControl
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModule
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModuleSupplement
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModuleComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryTerminal
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryComplete
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.OrbitAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.RecognitionAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.OmegaFixedAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.MathieuAt
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RemainingM22
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.MathieuExcluded

/-!
# Groups over F₂ and the TI case: elementary normalizer control

This module re-exports the elementary subgroup argument used in Lemma 12.2.6
and Notation 12.2.5(3e): a nontrivial subgroup of a TI subgroup `V` controls
normalizers inside `M`, and hence `H ∩ M = N_H(V)` if `N_G(V) ≤ M`.
The seven-module proof of 12.2.16, the guarded local split configuration,
and both terminal recognition branches now assemble all four alternatives
of 12.2.13 on every original chosen module at the same G,T. Only the earlier
structural and module inputs remain explicit, together with the standing
multiple-overgroup guard. The Chapter13 application supplies the actual
escaping centralizer after applying its ambient model exclusions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §12.2, printed pp. 794--807. The terminal recognition
step, Proposition 12.2.27, lies on p. 807. The source producers of the
structural and seven-case conclusions in 12.2.2 remain responsible for
discharging those inputs in the final classification.

The conditional structural assembly derives chosen-module existence,
reducedness and TI from independent normalization and the two surviving
FSU branches. These two source inputs remain explicit.
The ambient-local `Structural1222At` assembly accepts their actual
multiple-overgroup specializations and keeps the separate module and
recognition implications explicit.
-/
