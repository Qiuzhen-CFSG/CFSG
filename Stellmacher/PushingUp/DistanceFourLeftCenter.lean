module

public import Stellmacher.PushingUp.VertexOmegaGeneration

/-!
# The left shifted center at critical distance four

In the two-shift configuration of Stellmacher, *Pushing up* (1986), (3.3),
journal p.15, this module proves
`Z_(a-2) = (Z_(a-2) ∩ Z_(a-4)) [Z_(a-2), Z_(a+2)]`.
The full original pushing-up hypotheses and critical distance four are retained.

The length-two cores at the left shifted vertex are Sylows that generate its
stabilizer by (2.3). Their omega centers therefore generate its vertex center.
By (2.2)(d), one omega center is the endpoint commutator times the intrinsic
center part; the other is contained in both left vertex centers. The intrinsic
center part belongs to the latter omega center because it centralizes the whole
vertex stabilizer and has exponent two. These containments give the equality.

No symmetry of an arbitrary chosen configuration is assumed here, and neither
the vertex set nor the free amalgam is required to be finite.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem omega_sylowIn_le_vertexZ [Finite M]
    (S : Subgroup M) (a : Vertex S) (P : Subgroup (FreeAmalgam S))
    (hP : IsSylowSubgroupIn P (stabilizer S a)) :
    omegaOneCenterAmbient P ≤ vertexZ S a := by
  obtain ⟨PI, hPI⟩ := hP
  rw [← hPI]
  exact le_sSup ⟨PI, rfl⟩

private theorem sylowIn_le_for_decomposition
    {G : Type*} [Group G] {P H : Subgroup G} (h : IsSylowSubgroupIn P H) :
    P ≤ H := by
  obtain ⟨PI, hPI⟩ := h
  rw [← hPI]
  exact Subgroup.map_subtype_le _

set_option maxHeartbeats 600000 in
public theorem distanceFour_leftCenter_decomposition [Finite M]
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
    (hv : DistanceTwoShift.Conclusion S u c a v) :
    vertexZ S u = (vertexZ S u ⊓ vertexZ S v) ⊔
      ⁅vertexZ S u, vertexZ S c⁆ := by
  have hb : 0 < criticalDistance S := by omega
  have htwo : 2 < criticalDistance S := by omega
  have hua : (cosetGraph S).dist u a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hu.distance_two
  have hac : (cosetGraph S).dist a c = 2 := by
    have := hframe.left_length
    omega
  have hsecond : DistanceTwoShift.Frame S u c a := ⟨by omega, hac⟩
  let P := edgeTwoCore S u a
  let Q := edgeTwoCore S v u
  obtain ⟨hQa, hPEq⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    a a' c u hcrit htwo hframe hu
  obtain ⟨hQu, hQEq⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    u c a v hu.shifted_critical htwo hsecond hv
  obtain ⟨_, _, h22uc⟩ := criticalPair_sl2Two S T hTS hP hSne hA
    u c hu.shifted_critical hb
  obtain ⟨_, _, h22va⟩ := criticalPair_sl2Two S T hTS hP hSne hA
    v a hv.shifted_critical hb
  obtain ⟨_, _, hinp⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c hu.shifted_critical hb
  have hPGu : IsSylowSubgroupIn P (stabilizer S u) := by
    dsimp [P]
    rw [hPEq]
    exact h22uc.sourceSylow
  have hQGu : IsSylowSubgroupIn Q (stabilizer S u) :=
    distanceTwo_edgeCore_isSylow S T hTS u v hu.shifted_critical.1
      hv.shifted_critical.1 hv.distance_two
  have hQGv : IsSylowSubgroupIn Q (stabilizer S v) := by
    dsimp [Q]
    rw [hQEq]
    exact h22va.sourceSylow
  have hZcP : vertexZ S c ≤ P := by
    dsimp [P]
    rw [hPEq]
    exact le_sup_left
  have hgen : P ⊔ Q = stabilizer S u := by
    apply le_antisymm (sup_le (sylowIn_le_for_decomposition hPGu)
      (sylowIn_le_for_decomposition hQGu))
    rw [← hv.generates_left_stabilizer]
    exact sup_le le_sup_right (hZcP.trans le_sup_left)
  have hcomm : ⁅vertexZ S u, P⁆ ≤ omegaOneCenterAmbient P := by
    dsimp [P]
    rw [hPEq]
    exact criticalPair_sourceSylow_quadratic_ambient S T hTS hP hSne hA
      u c hu.shifted_critical hb
  have hZeq : vertexZ S u = omegaOneCenterAmbient P ⊔ omegaOneCenterAmbient Q :=
    vertexZ_eq_sup_omega_of_generating_sylows S u P Q hPGu hQGu hgen hcomm
  have hOQZu : omegaOneCenterAmbient Q ≤ vertexZ S u := by
    rw [hZeq]
    exact le_sup_right
  have hOQZv : omegaOneCenterAmbient Q ≤ vertexZ S v :=
    omega_sylowIn_le_vertexZ S v Q hQGv
  have hCuQ : vertexZ S u ⊓
      (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype ≤
      omegaOneCenterAmbient Q := by
    intro z hz
    have hzCoreData := (mem_omegaOneCenterAmbient_iff (vertexTwoCore S u) z).mp
      (hinp.left_Z_le_coreOmega hz.1)
    have hzQ : z ∈ Q := by
      dsimp [Q]
      rw [hQEq]
      exact hQu hzCoreData.1
    apply (mem_omegaOneCenterAmbient_iff Q z).mpr
    refine ⟨hzQ, hzCoreData.2.1, ?_⟩
    intro q hq
    obtain ⟨zi, hzi, hzieq⟩ := hz.2
    change (zi : FreeAmalgam S) = z at hzieq
    have hqGu := sylowIn_le_for_decomposition hQGu hq
    have hcent := (Subgroup.mem_center_iff.mp hzi) ⟨q, hqGu⟩
    have hamb := congrArg Subtype.val hcent
    simpa only [Subgroup.coe_mul, hzieq] using hamb
  have hOP : omegaOneCenterAmbient P =
      ⁅vertexZ S u, vertexZ S c⁆ ⊔
        (vertexZ S u ⊓
          (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype) := by
    dsimp [P]
    rw [hPEq]
    exact h22uc.sourceOmegaCenter
  apply le_antisymm
  · calc
      vertexZ S u = omegaOneCenterAmbient P ⊔ omegaOneCenterAmbient Q := hZeq
      _ ≤ (vertexZ S u ⊓ vertexZ S v) ⊔ ⁅vertexZ S u, vertexZ S c⁆ := ?_
    apply sup_le
    · rw [hOP]
      exact sup_le le_sup_right ((hCuQ.trans (le_inf hOQZu hOQZv)).trans le_sup_left)
    · exact (le_inf hOQZu hOQZv).trans le_sup_left
  · exact sup_le inf_le_left (hinp.critical.commutator_le_inf.trans inf_le_left)

end Stellmacher.PushingUp
