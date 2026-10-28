module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check01
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check02
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check03
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check04
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check05
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check06
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check07
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check08
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check09
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check10
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check11
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check12
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check13
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check14
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check15
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check16
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check17
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check18
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check19
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Check20

/-! Composition of the independently checked deduction ranges. Every prefix
premise is supplied by the preceding range; no certificate premise remains. -/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate
public theorem all_hold : ∀ n, n < 331989 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h16384 := all_hold_16384
  have h32768 := all_hold_32768 h16384
  have h49152 := all_hold_49152 h32768
  have h65536 := all_hold_65536 h49152
  have h81920 := all_hold_81920 h65536
  have h98304 := all_hold_98304 h81920
  have h114688 := all_hold_114688 h98304
  have h131072 := all_hold_131072 h114688
  have h147456 := all_hold_147456 h131072
  have h163840 := all_hold_163840 h147456
  have h180224 := all_hold_180224 h163840
  have h196608 := all_hold_196608 h180224
  have h212992 := all_hold_212992 h196608
  have h229376 := all_hold_229376 h212992
  have h245760 := all_hold_245760 h229376
  have h262144 := all_hold_262144 h245760
  have h278528 := all_hold_278528 h262144
  have h294912 := all_hold_294912 h278528
  have h311296 := all_hold_311296 h294912
  have h327680 := all_hold_327680 h311296
  have h331989 := all_hold_331989 h327680
  exact h331989
end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
