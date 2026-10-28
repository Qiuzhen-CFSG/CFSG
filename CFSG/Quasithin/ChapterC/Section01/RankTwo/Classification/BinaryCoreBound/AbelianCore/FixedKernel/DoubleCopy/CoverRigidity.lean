module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.Criteria
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.MixedClassification
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders

/-!
# Doubled-natural cover rigidity

Every cover of the doubled natural SL₃(2) module is an equivariant quotient
of two four-dimensional universal natural covers. Its fixed kernel has
dimension at most two. A nonzero kernel identifies the covering module with
either the mixed model U × V or the doubled model U × U.

Neither model admits an elementary abelian FF-offender in any faithful finite
overgroup normalizing the matrix-group image. These exclusions account for the
full linear normalizers, including operators mixing the summands. Consequently
the FF hypothesis forces the covering kernel to vanish. The theorem below
discharges every model obligation in the universal-cover reduction.

Source context: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.31(MS3), C.1.34(2),(5), printed pp.135–137, and I.1.5–6, printed p.408.
This is an independent representation-theoretic criterion used in the binary
MS two-copy branch, not a claim to prove the full source classification here.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy

/-- A commutator-generated cover of two natural binary SL₃(2) modules has
trivial kernel if a faithful finite overgroup normalizing the matrix-group
image acts on it as an FF-module. -/
theorem coverRigidity.{u, v} : CoverRigidity.{u, v} :=
  coverRigidity_of_model_results CoverModels.mixedClassification
    CoverModels.mixed_noFF CoverModels.doubled_noFF

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy
