module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalModels
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients

/-!
# From the concrete Rudvalis actions to the local quotient models

The actual max4 eight-group action and max6 five-block action are surjective.
The lower layer identifies their kernels with the intrinsic two-cores and
constructs multiplicative equivalences of the literal quotients. Applying
these certificates proves `localQuotientModels` with no remaining premises.

This discharges the marked local quotient input to the E.1.14(5) Rudvalis
assembly (printed p.214, citing Asc82a, Lemma 4.9), with local structures
from GLS3 Table 5.3r. The generating cover and its compatibility with
ambient extensions remain with the source-theorem assembly. No simplicity
or split-extension assumption is needed for these quotient calculations.
-/

namespace CFSG.Quasithin.ChapterE.Rudvalis

open _root_.Rudvalis.SylowOvergroups _root_.Rudvalis.CoreQuotients

/-- Conditional assembly of the intrinsic quotients from their two full-image actions. -/
public theorem localQuotientModels_of_actions
    (h4 : Function.Surjective max4EightAction)
    (f6 : max6 →* Equiv.Perm (Fin 5)) (h6 : Function.Surjective f6) :
    LocalQuotientModels :=
  ⟨⟨max4QuotientEquivOfFullImage h4⟩, ⟨max6QuotientEquivOfSurjective f6 h6⟩⟩

/-- The two marked Rudvalis local quotients are PSL₃(2) and S₅, respectively,
with both quotients taken by their intrinsic two-cores. -/
public theorem localQuotientModels : LocalQuotientModels :=
  localQuotientModels_of_actions max4EightAction_surjective
    max6FiveAction max6FiveAction_surjective

end CFSG.Quasithin.ChapterE.Rudvalis
