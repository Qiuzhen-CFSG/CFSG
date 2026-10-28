module
public import Stellmacher.PushingUp.DistanceFourCentralTwoElements
public import Theory.GroupTheory.CentralProductPSubgroupNormal

/-!
# Normality of the actual distance-four subgroup

In the chosen critical-distance-four configuration, the subgroup
`U = Z_a Z_c Z_u` is normal in the finite stabilizer `G_a`. This supplies
conjugation on the actual subgroup and its quotient by `Z_a`, as needed in
the final p = 2 contradiction.

The initial relations put U in the two-core of G_a. The source normality
calculation makes its product with the center normal, and the characteristic
Sylow obstruction places every central two-element in U. The generic
central-product normality lemma now applies directly. All original pushing-up
hypotheses are retained; finiteness is needed only for the stabilizer.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.3)(4)--(6), p.15.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

public theorem distanceFour_U_normal [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v) :
    ((DistanceFour.U S a c u).subgroupOf (stabilizer S a)).Normal := by
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  have hn := distanceFour_normality S T hTS hP hSne hA a a' c u v hb4 cfg
  let UI := (DistanceFour.U S a c u).subgroupOf (stabilizer S a)
  have hUIQ : UI ≤ pCore 2 (stabilizer S a) := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hi.U_le_core hz
    exact (Subtype.ext heq : w = z) ▸ hw
  exact Subgroup.normal_of_sup_center_normal UI
    ((pCore_isPGroup (p := 2) (G := stabilizer S a)).to_le hUIQ)
    hn.U_center_normal
    (distanceFour_central_two_elements_le_U S T hTS hP hSne hA a a' c u v hb4 cfg)

end Stellmacher.PushingUp
