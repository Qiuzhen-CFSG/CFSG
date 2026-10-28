module

public import Stellmacher.PushingUp.CriticalPairMiddleSylow

/-!
# The right center containment in the distance-four configuration

In a distance-four critical configuration, suppose the two length-two Sylow
subgroups at `c`, toward `a` and `a'`, generate its stabilizer. Then `Z_c`
is contained in `(Z_c ∩ Z_a') Z(G_a)`. This generation hypothesis is recorded
explicitly: in the chosen configuration it is supplied by a preceding
application of the distance-two shift, before reindexing the three shifts.

The imported middle-Sylow theorem identifies the edge core between `a` and
`c` with `Z_u Q_c`, using strict minimality and Sylow maximality.
Generation by the two Sylows therefore expresses `Z_c` as the join of their omega centers. Source (2.2)(d)
expresses the first omega center as `[Z_c,Z_u]` joined with the center part
at `c`. That center part lies in the second omega center, which lies in
`Z_c ∩ Z_a'`. The given shift places the remaining commutator in `Z(G_a)`.

This is the symmetric center containment in Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), (3.3), journal p. 15. No finiteness of the graph or
free amalgam is assumed; only the finite vertex stabilizers are used.
-/

namespace Stellmacher.PushingUp

open scoped commutatorElement
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

set_option maxHeartbeats 600000 in
/-- The middle-right Sylow generation equation gives the right center
containment used in the distance-four contradiction. -/
public theorem distanceFour_rightCenter_decomposition [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb4 : criticalDistance S = 4)
    (hframe : DistanceTwoShift.Frame S a a' c)
    (hu : DistanceTwoShift.Conclusion S a a' c u)
    (_hv : DistanceTwoShift.Conclusion S u c a v)
    (hgen : edgeTwoCore S a c ⊔ edgeTwoCore S a' c = stabilizer S c) :
    vertexZ S c ≤ (vertexZ S c ⊓ vertexZ S a') ⊔
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
  have hb : 0 < criticalDistance S := by omega
  have htwo : 2 < criticalDistance S := by omega
  have hac : (cosetGraph S).dist a c = 2 := by
    have := hframe.left_length
    omega
  obtain ⟨_, _, hinputs⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c hu.shifted_critical hb
  have hcu := hinputs.critical.reverse_critical
  obtain ⟨_, _, h22⟩ := criticalPair_sl2Two S T hTS hP hSne hA c u hcu hb
  obtain ⟨_, _, hcinp⟩ := criticalPair_actionInputs S T hTS hP hSne hA c u hcu hb
  have ha'Orbit :=
    (criticalPair_path T hTS hP hSne a a' hcrit hb).opposite_inMVertexOrbit
  let E := edgeTwoCore S a c
  let F := edgeTwoCore S a' c
  have hEc : IsSylowSubgroupIn E (stabilizer S c) :=
    distanceTwo_edgeCore_isSylow S T hTS c a hcu.1 hcrit.1 (by
      rw [SimpleGraph.dist_comm]; exact hac)
  have hFc : IsSylowSubgroupIn F (stabilizer S c) :=
    distanceTwo_edgeCore_isSylow S T hTS c a' hcu.1 ha'Orbit hframe.right_length
  have hFa' : IsSylowSubgroupIn F (stabilizer S a') := by
    have h := distanceTwo_edgeCore_isSylow S T hTS a' c ha'Orbit hcu.1 (by
      rw [SimpleGraph.dist_comm]; exact hframe.right_length)
    simpa [F, edgeTwoCore, inf_comm] using h
  have core_le (x : Vertex S) (P : Subgroup (FreeAmalgam S))
      (hSyl : IsSylowSubgroupIn P (stabilizer S x)) : vertexTwoCore S x ≤ P := by
    obtain ⟨PI, hPI⟩ := hSyl
    rw [← hPI]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := stabilizer S x)).le_sylow_of_normal PI)
  have hEsource : E = vertexZ S u ⊔ vertexTwoCore S c :=
    (criticalPair_middleSylow S T hTS hP hSne hA c u a hcu hb hcrit.1
      (by rw [SimpleGraph.dist_comm]; exact hac)
      (by rw [SimpleGraph.dist_comm, hu.distance_two, hb4]; omega)).1
  have hcomm : ⁅vertexZ S c, E⁆ ≤ omegaOneCenterAmbient E := by
    rw [hEsource]
    exact criticalPair_sourceSylow_quadratic_ambient S T hTS hP hSne hA c u hcu hb
  have hZeq : vertexZ S c = omegaOneCenterAmbient E ⊔ omegaOneCenterAmbient F :=
    vertexZ_eq_sup_omega_of_generating_sylows S c E F hEc hFc hgen hcomm
  have hOZ (x : Vertex S) (P : Subgroup (FreeAmalgam S))
      (hSyl : IsSylowSubgroupIn P (stabilizer S x)) :
      omegaOneCenterAmbient P ≤ vertexZ S x := by
    obtain ⟨PI, hPI⟩ := hSyl
    rw [← hPI]
    exact le_sSup ⟨PI, rfl⟩
  have hOF : omegaOneCenterAmbient F ≤ vertexZ S c ⊓ vertexZ S a' :=
    le_inf (hOZ c F hFc) (hOZ a' F hFa')
  have hCcF : vertexZ S c ⊓
      (Subgroup.center (stabilizer S c)).map (stabilizer S c).subtype ≤
        omegaOneCenterAmbient F := by
    intro z hz
    have hzData := (mem_omegaOneCenterAmbient_iff (vertexTwoCore S c) z).mp
      (hcinp.left_Z_le_coreOmega hz.1)
    apply (mem_omegaOneCenterAmbient_iff F z).mpr
    refine ⟨core_le c F hFc hzData.1, hzData.2.1, ?_⟩
    intro f hf
    obtain ⟨zI, hzI, hzEq⟩ := hz.2
    change (zI : FreeAmalgam S) = z at hzEq
    have hfGc : f ∈ stabilizer S c := by
      obtain ⟨PI, hPI⟩ := hFc
      rw [← hPI] at hf
      exact Subgroup.map_subtype_le _ hf
    have hcent := (Subgroup.mem_center_iff.mp hzI) ⟨f, hfGc⟩
    have hamb := congrArg Subtype.val hcent
    simpa only [Subgroup.coe_mul, hzEq] using hamb
  apply hZeq.le.trans
  apply sup_le
  · rw [hEsource, h22.sourceOmegaCenter]
    apply sup_le
    · rw [Subgroup.commutator_comm]
      exact (hu.commutator_central_of_two_lt htwo).trans le_sup_right
    · exact (hCcF.trans hOF).trans le_sup_left
  · exact hOF.trans le_sup_left

end Stellmacher.PushingUp
