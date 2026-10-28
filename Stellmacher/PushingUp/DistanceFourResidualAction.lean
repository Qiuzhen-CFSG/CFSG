module

public import Stellmacher.PushingUp.DistanceFourInitialRelations
public import Stellmacher.PushingUp.ResidualNeighborTransport
public import Theory.GroupAction.Quotient

/-!
# Nontrivial residual action on the distance-four quotient

This module proves the geometric obstruction in Stellmacher, *Pushing up*
(1986), (3.3)(6): the 2-residual of `G_a` cannot fix the actual quotient
`U/Z_a` under an action induced by ambient conjugation. The action and its
compatibility are explicit, so callers retain their exact action instance.
The final graph assembly constructs that action after proving `U` normal.

A residual element moves the left shifted vertex to distance at most two from
the right shifted vertex. The right graph action makes the corresponding
center the conjugate by the inverse group element. Strict-distance minimality
puts this conjugated center in the right vertex core, so it commutes with the
right center. Trivial quotient action would make every original left-center
element differ from its conjugate by `Z_a`, which also commutes with the right
center. This contradicts the nontrivial endpoint commutator `Y`.

A corollary says the quotient-action image is not a 2-group: a 2-group image
has a kernel of 2-power index, and the residual lies in every such normal
kernel. Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), p.15.
No finite vertex-set or finite free-amalgam assumption is made.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

set_option maxHeartbeats 700000 in
public theorem distanceFour_residual_not_fix_quotient [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v)
    (hZn : ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).Normal)
    [MulDistribMulAction (stabilizer S a)
      ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))]
    (hconjU : ∀ g : stabilizer S a, ∀ w : DistanceFour.U S a c u,
      (g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹ ∈ DistanceFour.U S a c u)
    (hact : ∀ (g : stabilizer S a) (w : DistanceFour.U S a c u),
      g • (QuotientGroup.mk' ((vertexZ S a).subgroupOf (DistanceFour.U S a c u))) w =
        (QuotientGroup.mk' ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)))
          ⟨(g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹, hconjU g w⟩) :
    ¬ twoResidualAmbient (⊤ : Subgroup (stabilizer S a)) ≤
      fixingSubgroup (stabilizer S a) (Set.univ : Set
        ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))) := by
  intro hfix
  let U := DistanceFour.U S a c u
  let Z := (vertexZ S a).subgroupOf U
  let q := QuotientGroup.mk' Z
  have hb : 0 < criticalDistance S := by omega
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  have hac : (cosetGraph S).dist a c = 2 := by
    have := cfg.first_frame.left_length
    omega
  obtain ⟨g, hg, hdist⟩ := residual_moves_distance_two_vertices_close S T hTS
    a u c cfg.critical.1 cfg.first_shift.distance_two hac
  obtain ⟨r, hr, rfl⟩ := hg
  change (cosetGraph S).dist (act S (r : FreeAmalgam S) u) c ≤ 2 at hdist
  have hrinv : r⁻¹ ∈ twoResidualAmbient (⊤ : Subgroup (stabilizer S a)) :=
    (twoResidualAmbient (⊤ : Subgroup (stabilizer S a))).inv_mem hr
  have hrfix := hfix hrinv
  have huMoved : InMVertexOrbit S (act S (r : FreeAmalgam S) u) := by
    obtain ⟨x, hxu⟩ := cfg.first_shift.shifted_critical.1
    refine ⟨x * (r : FreeAmalgam S), ?_⟩
    rw [act_mul, ← hxu]
  have huc := criticalPair_path T hTS hP hSne u c cfg.first_shift.shifted_critical hb
  have hcAdj : ∃ d : Vertex S, Adjacent S c d := by
    obtain ⟨x, hxc⟩ := huc.opposite_inMVertexOrbit
    refine ⟨act S x (hVertex S 1), ?_⟩
    rw [hxc]
    exact (adjacent_act_iff S x (mVertex S 1) (hVertex S 1)).2 (base_adjacent S)
  obtain ⟨d, hcd⟩ := hcAdj
  have hMovedCore : vertexZ S (act S (r : FreeAmalgam S) u) ≤ vertexTwoCore S c := by
    rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS c d
      huc.opposite_inMVertexOrbit hcd]
    apply vertexZ_le_neighborhoodKernel_of_dist_lt S huMoved
    omega
  obtain ⟨_, _, hinp⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c cfg.first_shift.shifted_critical hb
  have hZuU : vertexZ S u ≤ U := le_sup_right
  have hZcU : vertexZ S c ≤ U := le_sup_right.trans le_sup_left
  have hcommute : vertexZ S u ≤ Subgroup.centralizer (vertexZ S c) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    let zu : U := ⟨z, hZuU hz⟩
    let zm : U := ⟨((r⁻¹ : stabilizer S a) : FreeAmalgam S) * (zu : FreeAmalgam S) *
      ((r⁻¹ : stabilizer S a) : FreeAmalgam S)⁻¹, hconjU r⁻¹ zu⟩
    have hzmVertex : (zm : FreeAmalgam S) ∈ vertexZ S (act S (r : FreeAmalgam S) u) := by
      rw [vertexZ_act_eq_map]
      refine ⟨z, hz, ?_⟩
      simp [zm, zu]
    have hzmw : (zm : FreeAmalgam S) * w = w * zm :=
      (mem_omegaOneCenterAmbient_iff _ w).mp (hinp.right_Z_le_coreOmega hw)
        |>.2.2 zm (hMovedCore hzmVertex)
    have hquot : q zm = q zu := by
      calc
        q zm = r⁻¹ • q zu := (hact r⁻¹ zu).symm
        _ = q zu := ((mem_fixingSubgroup_iff (M := stabilizer S a) (s := Set.univ)).mp hrfix) (q zu) (Set.mem_univ _)
    obtain ⟨k, hk, heq⟩ := (QuotientGroup.mk'_eq_mk' (N := Z)).mp hquot
    have hkZa : (k : FreeAmalgam S) ∈ vertexZ S a := hk
    have hkw : (k : FreeAmalgam S) * w = w * k :=
      hi.Z_centralizes_U k hkZa w (hZcU hw)
    have hfactor : (zm : FreeAmalgam S) * k = z := congrArg Subtype.val heq
    rw [← hfactor]
    calc
      w * ((zm : FreeAmalgam S) * k) = (w * zm) * k := (mul_assoc _ _ _).symm
      _ = ((zm : FreeAmalgam S) * w) * k := by rw [hzmw]
      _ = (zm : FreeAmalgam S) * (w * k) := mul_assoc _ _ _
      _ = (zm : FreeAmalgam S) * (k * w) := by rw [hkw]
      _ = ((zm : FreeAmalgam S) * k) * w := (mul_assoc _ _ _).symm
  exact hi.Y_ne_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcommute)


private theorem residual_le_fix_of_image_isPGroup
    {G W : Type*} [Group G] [Finite G] [Group W]
    [MulDistribMulAction G W]
    (hp : IsPGroup 2 (MulDistribMulAction.toMulAut G W).range) :
    twoResidualAmbient (⊤ : Subgroup G) ≤ fixingSubgroup G (Set.univ : Set W) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := MulDistribMulAction.toMulAut G W
  let K := f.ker
  have hquot : IsPGroup 2 (G ⧸ K) :=
    hp.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hquot
  let KI := K.subgroupOf (⊤ : Subgroup G)
  have hKIindex : KI.index = 2 ^ n := by
    calc
      KI.index = K.relIndex ⊤ := rfl
      _ = K.index := Subgroup.relIndex_top_right K
      _ = Nat.card (G ⧸ K) := Subgroup.index_eq_card K
      _ = 2 ^ n := hn
  have hle : twoResidualSubgroup (⊤ : Subgroup G) ≤ KI :=
    sInf_le ⟨inferInstance, n, hKIindex⟩
  rw [fixingSubgroup_univ_eq_ker_toMulAut]
  calc
    twoResidualAmbient (⊤ : Subgroup G) =
        (twoResidualSubgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := rfl
    _ ≤ KI.map (⊤ : Subgroup G).subtype := Subgroup.map_mono hle
    _ = K := Subgroup.map_subgroupOf_eq_of_le le_top

set_option maxHeartbeats 700000 in
public theorem distanceFour_action_image_not_two [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v)
    (hZn : ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).Normal)
    [MulDistribMulAction (stabilizer S a)
      ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))]
    (hconjU : ∀ g : stabilizer S a, ∀ w : DistanceFour.U S a c u,
      (g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹ ∈ DistanceFour.U S a c u)
    (hact : ∀ (g : stabilizer S a) (w : DistanceFour.U S a c u),
      g • (QuotientGroup.mk' ((vertexZ S a).subgroupOf (DistanceFour.U S a c u))) w =
        (QuotientGroup.mk' ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)))
          ⟨(g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹, hconjU g w⟩) :
    ¬ IsPGroup 2 (MulDistribMulAction.toMulAut (stabilizer S a)
      ((DistanceFour.U S a c u) ⧸ (vertexZ S a).subgroupOf (DistanceFour.U S a c u))).range := by
  intro hp
  exact distanceFour_residual_not_fix_quotient S T hTS hP hSne hA
    a a' c u v hb4 cfg hZn hconjU hact (residual_le_fix_of_image_isPGroup hp)

end Stellmacher.PushingUp
