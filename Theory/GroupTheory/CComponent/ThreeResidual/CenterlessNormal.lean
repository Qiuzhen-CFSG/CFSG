module
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
import all Theory.GroupTheory.CComponent.ThreeResidual

/-!
# A centerless normal subgroup exhausts the cubic residual

The rank-two centralizer and outer-index arguments in the parent module do
not require the subgroup to be a C-component. This intentional internal
extension reuses those private arguments at their centerless normal-subgroup
interface. Intrinsic cubic generation then identifies the prime-to-three
residual, retaining the actual subgroup embedding.

Source: Aschbacher–Smith A.3.18 and the two-A₃ product in 13.5.6, pp.51,917.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem primeToResidual_eq_of_centerless_normal_rank_two
    (X : Subgroup G) [X.Normal] (hz : center X = ⊥)
    (hr : 2 ≤ primeRank 3 X) (hG : primeRank 3 G ≤ 2)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer X)))
    (hg : primeToResidual 3 X = ⊤) : primeToResidual 3 G = X := by
  exact primeToResidual_eq_of_subnormal_coprime_index 3 X
    (inferInstance : X.Normal).isSubnormal hg
    (index_coprime_of_centralizer_outer X (centralizer_coprime_of_rank X hz hr hG) ho)
end Theory.GroupTheory
