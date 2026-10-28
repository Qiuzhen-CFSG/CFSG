module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Words
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Data

/-!
# Comparison with the shared max4 words

Expanding the fourteen binary exponents identifies the small word data with
exactly Max4Words.generator. The data and finite certificate modules need no
imports of the intrinsic core or its quotient actions.
Source: the fixed ATLAS words in Max4Geometry.Words; GLS3 Table 5.3r.
-/

namespace Rudvalis.CoveringIncidence.Max4Special
open SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate Collection

public theorem generator_eq (i : Fin 11) : Max4Words.generator i = eval (word i) := by
  fin_cases i <;> norm_num [Max4Words.generator, Max4Words.masks, normalForm, word, eval,
    List.ofFn_succ, Fin.val_zero, Fin.val_succ] <;> rfl

end Rudvalis.CoveringIncidence.Max4Special
