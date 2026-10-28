module
public import Theory.SpecificGroups.BinaryLinear.ThreeFreeSylowOvergroups
public import Theory.GroupTheory.SylowInvariantThreeFree.Overgroups

/-!
# Three-free subgroups normalized by a binary linear Sylow subgroup

If a subgroup of GL(n,2) has order prime to three and is normalized by a
full Sylow two-subgroup S, its product with S still has order prime to
three. The binary flag overgroup theorem identifies this product with S.
Thus the original subgroup is a two-group. This is the precise model
input for the L₄(2) and L₅(2) centralizer argument in Aschbacher--Smith
8.3.8, printed p.725.
-/

public section
open Subgroup
namespace BinaryLinear.ThreeFreeSylowOvergroups

/-- Every three-free subgroup normalized by a full binary Sylow is a two-group. -/
theorem normalized_three_free_isPGroup {m : ℕ}
    (S : Sylow 2 (BinaryLinear.OuterCyclic.LinearGroup (m+1)))
    (V : Subgroup (BinaryLinear.OuterCyclic.LinearGroup (m+1)))
    (hnorm : (S : Subgroup _) ≤ normalizer (V : Set (BinaryLinear.OuterCyclic.LinearGroup (m+1))))
    (hthree : ¬ 3 ∣ Nat.card V) : IsPGroup 2 V := by
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup (m+1)) := Finite.of_injective
    (fun g : BinaryLinear.OuterCyclic.LinearGroup (m+1) =>
      (g : BinaryLinear.OuterCyclic.Space (m+1) → BinaryLinear.OuterCyclic.Space (m+1)))
    DFunLike.coe_injective
  exact Theory.GroupTheory.isPGroup_of_three_free_sylow_overgroups S V hnorm hthree
    (eq_sylow_of_three_free S)

end BinaryLinear.ThreeFreeSylowOvergroups
