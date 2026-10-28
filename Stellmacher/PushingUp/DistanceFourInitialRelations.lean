module

public import Stellmacher.PushingUp.DistanceFourConfiguration
public import Stellmacher.PushingUp.ShiftSharedSylow

/-!
# Initial group relations at critical distance four

For the chosen source configuration, this module proves that `U ≤ Q_a`,
`Y ≠ 1`, `Y ≤ Z(G_a)`, `Z_a` centralizes `U`, an involution lies in
`U \ Z_a`, and `F Q_a = G_a`.

Strict-distance containment and the local kernel/core identity put all three
center factors in `Q_a`. The shifted critical pair supplies nontriviality and
centrality of `Y`; the core omega containment for `Z_a` gives centralization.
If the right center factor lay in `Z_a`, its commutator with the left factor
would vanish, producing the outside involution. Finally reverse (2.2)(a) at
`(a-4,a)` identifies the first length-two edge core with `Z_(a-4) Q_a`;
the first shift generation equation then gives the actor generation.

Source: B. Stellmacher, *Pushing up* (1986), the configuration and initial
relations of (3.3), journal p.15. All source subgroups are the literal
abbreviations from `DistanceFourConfiguration`, and only vertex stabilizers
are assumed finite.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem adjacent_for_initial (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) : ∃ d : Vertex S, Adjacent S a d := by
  obtain ⟨g, rfl⟩ := ha
  exact ⟨act S g (hVertex S 1),
    (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2 (base_adjacent S)⟩

private theorem strict_core_for_initial [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x y : Vertex S) (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hlt : (cosetGraph S).dist x y < criticalDistance S) :
    vertexZ S x ≤ vertexTwoCore S y := by
  obtain ⟨d, hyd⟩ := adjacent_for_initial S y hy
  rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS y d hy hyd]
  exact vertexZ_le_neighborhoodKernel_of_dist_lt S hx hlt

private theorem sylow_maximal_for_initial
    {G : Type*} [Group G] (P E H : Subgroup G)
    (hP : IsSylowSubgroupIn P H)
    (hPE : P ≤ E) (hEH : E ≤ H) (hEp : IsPGroup 2 E) : E = P := by
  obtain ⟨T, hT⟩ := hP
  let EI := E.subgroupOf H
  have hEIp : IsPGroup 2 EI :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  have hTE : (T : Subgroup H) ≤ EI := by
    intro t ht
    apply hPE
    rw [← hT]
    exact Subgroup.mem_map_of_mem H.subtype ht
  have hEq := T.is_maximal' hEIp hTE
  have hMap := congrArg (Subgroup.map H.subtype) hEq
  rw [Subgroup.map_subgroupOf_eq_of_le hEH, hT] at hMap
  exact hMap

public structure DistanceFour.InitialRelations (S : Subgroup M) (a a' c u v : Vertex S) : Prop where
  U_le_core : DistanceFour.U S a c u ≤ vertexTwoCore S a
  Y_ne_bot : DistanceFour.Y S u c ≠ ⊥
  Y_le_center : DistanceFour.Y S u c ≤
    (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype
  Z_centralizes_U : ∀ z ∈ vertexZ S a, ∀ w ∈ DistanceFour.U S a c u, z * w = w * z
  outside_involution : ∃ x : FreeAmalgam S,
    x ∈ DistanceFour.U S a c u ∧ x ∉ vertexZ S a ∧ x ^ 2 = 1
  F_generates_modulo_core : DistanceFour.F S a' v ⊔ vertexTwoCore S a = stabilizer S a

set_option maxHeartbeats 600000 in
public theorem distanceFour_initialRelations [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (hconf : DistanceFour.Configuration S a a' c u v) :
    DistanceFour.InitialRelations S a a' c u v := by
  have hb : 0 < criticalDistance S := by omega
  have htwo : 2 < criticalDistance S := by omega
  have hcrit := hconf.critical
  have hu := hconf.first_shift
  have hv := hconf.second_shift
  have hac : (cosetGraph S).dist a c = 2 := by
    have := hconf.first_frame.left_length
    omega
  obtain ⟨_, _, hAA'⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    a a' hcrit hb
  obtain ⟨_, _, hUC⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c hu.shifted_critical hb
  obtain ⟨_, _, hVA⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    v a hv.shifted_critical hb
  have hc := (criticalPair_path T hTS hP hSne u c hu.shifted_critical hb)
    |>.opposite_inMVertexOrbit
  have hZaQa : vertexZ S a ≤ vertexTwoCore S a := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ z).mp (hAA'.left_Z_le_coreOmega hz)).1
  have hZcQa : vertexZ S c ≤ vertexTwoCore S a :=
    strict_core_for_initial S T hTS c a hc hcrit.1 (by
      rw [SimpleGraph.dist_comm]
      omega)
  have hZuQa : vertexZ S u ≤ vertexTwoCore S a :=
    strict_core_for_initial S T hTS u a hu.shifted_critical.1 hcrit.1 (by
      rw [SimpleGraph.dist_comm]
      have := hu.distance_two
      omega)
  have hUQa : DistanceFour.U S a c u ≤ vertexTwoCore S a :=
    sup_le (sup_le hZaQa hZcQa) hZuQa
  have hZaCentral : ∀ z ∈ vertexZ S a, ∀ w ∈ DistanceFour.U S a c u,
      z * w = w * z := by
    intro z hz w hw
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp
      (hAA'.left_Z_le_coreOmega hz) |>.2.2 w (hUQa hw)).symm
  have hYne : DistanceFour.Y S u c ≠ ⊥ := hUC.critical.commutator_ne_bot
  have hZcNotZa : ¬ vertexZ S c ≤ vertexZ S a := by
    intro hle
    apply hYne
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hZaCentral w (hle hw) z ((show vertexZ S u ≤ DistanceFour.U S a c u from le_sup_right) hz)
  obtain ⟨x, hxc, hxa⟩ := SetLike.not_le_iff_exists.mp hZcNotZa
  have hxU : x ∈ DistanceFour.U S a c u := (show vertexZ S c ≤ DistanceFour.U S a c u from le_sup_right.trans le_sup_left) hxc
  have hxSq : x ^ 2 = 1 :=
    (mem_omegaOneCenterAmbient_iff _ x).mp (hUC.right_Z_le_coreOmega hxc) |>.2.1
  have hZvQu : vertexZ S v ≤ vertexTwoCore S u :=
    strict_core_for_initial S T hTS v u hv.shifted_critical.1
      hu.shifted_critical.1 (by
        rw [SimpleGraph.dist_comm]
        have := hv.distance_two
        omega)
  obtain ⟨hQaE, hEeq⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    a a' c u hcrit htwo hconf.first_frame hu
  obtain ⟨_, _, h22AV⟩ := criticalPair_sl2Two S T hTS hP hSne hA
    a v hVA.critical.reverse_critical hb
  have hPE : vertexZ S v ⊔ vertexTwoCore S a ≤ edgeTwoCore S u a := by
    rw [hEeq]
    exact sup_le (hZvQu.trans le_sup_right) hQaE
  have hEG : edgeTwoCore S u a ≤ stabilizer S a :=
    (Subgroup.map_subtype_le (pCore 2 ↥(stabilizer S u ⊓ stabilizer S a))).trans
      inf_le_right
  have hEp : IsPGroup 2 (edgeTwoCore S u a) :=
    (pCore_isPGroup (p := 2) (G := ↥(stabilizer S u ⊓ stabilizer S a))).map
      (stabilizer S u ⊓ stabilizer S a).subtype
  have hE : edgeTwoCore S u a = vertexZ S v ⊔ vertexTwoCore S a :=
    sylow_maximal_for_initial _ _ _ h22AV.sourceSylow hPE hEG hEp
  have hgen : DistanceFour.F S a' v ⊔ vertexTwoCore S a = stabilizer S a := by
    have h := hu.generates_left_stabilizer
    rw [hE] at h
    convert h using 1
    dsimp [DistanceFour.F]
    ac_rfl
  exact ⟨hUQa, hYne, hu.commutator_central_of_two_lt htwo,
    hZaCentral, ⟨x, hxU, hxa, hxSq⟩, hgen⟩

end Stellmacher.PushingUp
