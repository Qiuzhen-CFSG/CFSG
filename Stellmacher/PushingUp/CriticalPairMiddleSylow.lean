module

public import Stellmacher.PushingUp.VertexOmegaGeneration

/-!
# The Sylow subgroup shared through a middle vertex

For a positive critical pair `(x,z)`, let `y` be an M-side vertex at distance
two from `x` and at distance strictly less than the critical distance from
`z`. Then the length-two edge core between `y` and `x` is `Z_z Q_x`, and
it contains `Q_y`. These identities transport the local Sylow descriptions
through the middle vertices of the distance-four configuration.

Strict minimality places `Z_z` in the neighborhood kernel at `y`, which
is `Q_y`. The edge core is Sylow in both endpoint stabilizers, so it contains
both `Q_y` and `Q_x`, hence `Z_z Q_x`. Source (2.2)(a) makes this latter
group Sylow in `G_x`; maximality yields equality. The neighboring-core
inclusion then follows from its containment in the shared Sylow.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.2)(a) and
the shared-Sylow calculations in (3.3)(1). No finite graph or free-amalgam
assumption is used.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M]

/-- A middle vertex identifies the shared edge Sylow with the critical-pair
source Sylow, and places its own core inside it. -/
public theorem criticalPair_middleSylow [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (x z y : Vertex S) (hcrit : IsCriticalPair S x z)
    (hb : 0 < criticalDistance S) (hy : InMVertexOrbit S y)
    (hxy : (cosetGraph S).dist x y = 2)
    (hzy : (cosetGraph S).dist z y < criticalDistance S) :
    edgeTwoCore S y x = vertexZ S z ⊔ vertexTwoCore S x ∧
      vertexTwoCore S y ≤ vertexZ S z ⊔ vertexTwoCore S x := by
  obtain ⟨_, _, h22⟩ := criticalPair_sl2Two S T hTS hP hSne hA x z hcrit hb
  have hz := (criticalPair_path T hTS hP hSne x z hcrit hb).opposite_inMVertexOrbit
  let E := edgeTwoCore S y x
  have hEx : IsSylowSubgroupIn E (stabilizer S x) :=
    distanceTwo_edgeCore_isSylow S T hTS x y hcrit.1 hy hxy
  have hEy : IsSylowSubgroupIn E (stabilizer S y) := by
    have h := distanceTwo_edgeCore_isSylow S T hTS y x hy hcrit.1 (by
      rw [SimpleGraph.dist_comm]; exact hxy)
    simpa [E, edgeTwoCore, inf_comm] using h
  have core_le (a : Vertex S) (P : Subgroup (FreeAmalgam S))
      (hSyl : IsSylowSubgroupIn P (stabilizer S a)) : vertexTwoCore S a ≤ P := by
    obtain ⟨PI, hPI⟩ := hSyl
    rw [← hPI]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := stabilizer S a)).le_sylow_of_normal PI)
  have hZzQy : vertexZ S z ≤ vertexTwoCore S y := by
    obtain ⟨g, hg⟩ := hy
    have hyd : Adjacent S y (act S g (hVertex S 1)) := by
      rw [hg]
      exact (adjacent_act_iff S g _ _).mpr (base_adjacent S)
    rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS y _ ⟨g, hg⟩ hyd]
    exact vertexZ_le_neighborhoodKernel_of_dist_lt S hz hzy
  have hPE : vertexZ S z ⊔ vertexTwoCore S x ≤ E :=
    sup_le (hZzQy.trans (core_le y E hEy)) (core_le x E hEx)
  have hEsource : E = vertexZ S z ⊔ vertexTwoCore S x := by
    obtain ⟨PI, hPI⟩ := h22.sourceSylow
    obtain ⟨EI, hEI⟩ := hEx
    have hle : (PI : Subgroup (stabilizer S x)) ≤ EI := by
      apply (Subgroup.map_le_map_iff_of_injective (stabilizer S x).subtype_injective).mp
      rwa [hPI, hEI]
    have heq : (EI : Subgroup (stabilizer S x)) = PI :=
      PI.is_maximal' EI.isPGroup' hle
    rw [← hEI, heq, hPI]
  exact ⟨hEsource, (core_le y E hEy).trans_eq hEsource⟩

end Stellmacher.PushingUp
