module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.PermutationComparison
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# Representative outer centralizer in the Hall--Janko carrier

`fixedEquivModel` identifies the entire fixed subgroup, with a faithful action
and surjectivity onto the explicit fourteen-point model. Its order is 336.
The independent identification of this concrete small model with PGL₂(7)
remains explicit below; the source theorem is not yet asserted unconditionally.

Sources: GLS3 Table 5.3g, class 2C; Aschbacher--Smith 16.1.5(8), p.1172.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
open ExceptionalParabolics

/-- Application of the small-model comparison to the exact source carrier. -/
theorem representative_equiv_of_model
    (e : model ≃* GorensteinWalter.PGL2 (ZMod 7)) :
    Nonempty (involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7)) :=
  ⟨fixedEquivModel.trans e⟩

end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
