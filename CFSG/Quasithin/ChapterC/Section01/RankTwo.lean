module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupAction.CentralElementaryLift

/-!
# Rank-two pushing-up: initial structural reductions

This module supplies the elementary MS-pair ingredients and the lift argument
used in C.1.35. The classification C.1.32/34 and the complete refinements
C.1.35/36 remain to be assembled from their substantial prerequisites.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.30–36, printed pp.135–141.
-/

namespace CFSG.Quasithin.ChapterC

/-- The elementary-lift step of C.1.35, with its precise stabilizer input.
For a natural central module and a dual quotient summand, the concrete
linear-group calculation must establish `hdual` before this is applied. -/
public theorem rankTwo_elementary_lift
    {L W : Type*} [Group L] [Group W] [MulDistribMulAction L W]
    (U : Subgroup W) (hcentral : U ≤ Subgroup.center W)
    [IsElementaryAbelian 2 U] (hsquare : ∀ w : W, w ^ 2 ∈ U)
    (hdual : ∀ w : W, w ∉ U → ∀ u ∈ U,
      (∀ l : L, (l • w) / w ∈ U → l • u = u) → u = 1) :
    IsElementaryAbelian 2 W :=
  IsElementaryAbelian.of_central_kernel_stabilizer U hcentral
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) hsquare hdual

end CFSG.Quasithin.ChapterC
