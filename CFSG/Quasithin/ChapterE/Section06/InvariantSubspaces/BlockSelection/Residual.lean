module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.Generation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.IndexContracts

/-!
# Residual identification from the two index calculations

The intrinsic generation theorem puts every selected block in O^{3′}(H).
For the reverse inclusion, index prime to three and subnormality identify
the block with the residual along its subnormal chain. Normality is a
consequence, and is not an extra assumption on the E.6.7 decomposition.

The two index calculations are still explicit inputs. This is conditional
assembly of `SingleResidualInput`, not a completed derivation from
Hypothesis E.6.1 and E.6.7. Both source alternatives must be discharged by
the index owners before the residual task is complete.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof of
E.6.14, printed p.251 (PDF p.262).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G]

/-- The complete residual implication once both source-branch index
calculations have been supplied. -/
theorem singleResidualInput_of_index_inputs {T : Sylow 2 G} {M V : Subgroup G}
    (hlow : LowRankIndexInput T M V) (hfaithful : FaithfulIndexInput T M V) :
    SingleResidualInput T M V := by
  intro W hW hc hthree d hcount i
  apply chiZero_eq_primeToResidual_of_index (d.le i) (d.type i) (d.subnormal i)
  rcases hthree with hr | ha
  · exact hlow W hW hc hr d hcount i
  · exact hfaithful W hW hc ha d hcount i

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
