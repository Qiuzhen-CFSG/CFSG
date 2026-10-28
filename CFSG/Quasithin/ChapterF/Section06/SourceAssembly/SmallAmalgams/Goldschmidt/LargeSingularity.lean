module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeLocalOrders
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.WeissEven

/-!
# Odd least singularity in the large local residual branch

The actual local residual exclusions imply a vertex stabilizer larger than
twenty-four. The proved Weiss even-singularity bound then makes the least
singularity index odd. The output retains its minimality and a singular arc
on the original cubic tree; no order or parity premise is added.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.3), p.393.
The exclusion of the remaining odd lengths one and three belongs to (4.4).
-/

public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Goldschmidt (4.3), retaining an actual least singular arc for the
subsequent small-length exclusion. -/
theorem CubicTreeAction.exists_odd_singularityIndex_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4))) :
    ∃ s : ℕ, 0 < s ∧ Odd s ∧
      (∀ (k : ℕ) (v : RankTwo.Vertex F) (q : BasedWalk (RankTwo.graph F) k v),
        k < s → q.Nonbacktracking → RightRegular (A := G) q) ∧
      ∃ (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) s v),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p :=
  h.exists_odd_singularityIndex_of_large (base F false)
    (h.stabilizer_card_gt_twentyFour_of_large_residual hC hA (base F false))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
