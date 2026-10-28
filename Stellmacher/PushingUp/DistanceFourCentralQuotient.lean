module

public import Stellmacher.PushingUp.DistanceFourInitialRelations
public import Stellmacher.PushingUp.CriticalPairCoreIntersectionData
public import Stellmacher.PushingUp.CriticalPairMiddleSylow
public import Theory.GroupTheory.CenterSmallIndex
public import Theory.GroupTheory.CentralTwoFactorQuotient

/-!
# The actual center and central quotient at critical distance four

For Stellmacher's distance-four configuration, the literal finite subgroup
`U = Z_a Z_c Z_u` has center `Z_a` and quotient of order four. The supporting
quotient theorem proves that `U/Z_a` is elementary abelian using the caller's
chosen normality instance. This identifies the actual central kernel needed
by the later conjugation action; it assumes no normality of `U` in `G_a`.

The middle-vertex Sylows identify `Z_u ∩ Z_a` with `Z_u ∩ Q_c` and similarly
`Z_c ∩ Z_a` with `Z_c ∩ Q_u`. The critical-pair fixed-line theorem gives each
intersection relative index two. Since `[Z_u,Z_c] ≤ Z_u ∩ Z_c`, the first
identification also puts the commutator in `Z_a`. Thus the two elementary
factor images generate an elementary quotient of order at most four.
`Z_a` centralizes `U`, whereas its two noncentral factors have nontrivial
commutator. The central-small-index theorem therefore forces `Z(U) = Z_a`
and index exactly four. Finiteness is transported from the vertex stabilizer,
without assuming that the free amalgam or its graph is finite.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.3)(6) to (f),
journal p.15, with the exact critical-pair omega-center calculations from
(1.4)(a) and (2.2). All ambient subgroups are the production definitions in
`DistanceFourConfiguration`.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem strict_core [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x y : Vertex S) (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hlt : (cosetGraph S).dist x y < criticalDistance S) :
    vertexZ S x ≤ vertexTwoCore S y := by
  obtain ⟨g, hg⟩ := hy
  have hyd : Adjacent S y (act S g (hVertex S 1)) := by
    rw [hg]
    exact (adjacent_act_iff S g _ _).mpr (base_adjacent S)
  rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS y _ ⟨g, hg⟩ hyd]
  exact vertexZ_le_neighborhoodKernel_of_dist_lt S hx hlt

private theorem omega_le_vertex
    (S : Subgroup M) (a : Vertex S) (P : Subgroup (FreeAmalgam S))
    (hP : IsSylowSubgroupIn P (stabilizer S a)) :
    omegaOneCenterAmbient P ≤ vertexZ S a := by
  obtain ⟨PI, hPI⟩ := hP
  rw [← hPI]
  exact le_sSup ⟨PI, rfl⟩

private theorem intersection_data [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v) :
    (vertexZ S a).relIndex (vertexZ S u) = 2 ∧
    (vertexZ S a).relIndex (vertexZ S c) = 2 ∧
    DistanceFour.Y S u c ≤ vertexZ S a := by
  have hb : 0 < criticalDistance S := by omega
  have hau : (cosetGraph S).dist a u = 2 := cfg.first_shift.distance_two
  have hac : (cosetGraph S).dist a c = 2 := by
    have := cfg.first_frame.left_length
    omega
  obtain ⟨_, _, hinp⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c cfg.first_shift.shifted_critical hb
  have hc := hinp.critical.reverse_critical.1
  have hu := cfg.first_shift.shifted_critical.1
  have ha := cfg.critical.1
  have hZaQc := strict_core S T hTS a c ha hc (by omega)
  have hZaQu := strict_core S T hTS a u ha hu (by omega)
  obtain ⟨hEu, _⟩ := criticalPair_middleSylow S T hTS hP hSne hA
    u c a cfg.first_shift.shifted_critical hb ha
    (by rwa [SimpleGraph.dist_comm]) (by rw [SimpleGraph.dist_comm]; omega)
  obtain ⟨hEc, _⟩ := criticalPair_middleSylow S T hTS hP hSne hA
    c u a hinp.critical.reverse_critical hb ha
    (by rwa [SimpleGraph.dist_comm]) (by rw [SimpleGraph.dist_comm]; omega)
  have hOuZa : omegaOneCenterAmbient (vertexZ S c ⊔ vertexTwoCore S u) ≤ vertexZ S a := by
    rw [← hEu]
    apply omega_le_vertex
    simpa only [edgeTwoCore, inf_comm] using
      distanceTwo_edgeCore_isSylow S T hTS a u ha hu hau
  have hOcZa : omegaOneCenterAmbient (vertexZ S u ⊔ vertexTwoCore S c) ≤ vertexZ S a := by
    rw [← hEc]
    apply omega_le_vertex
    simpa only [edgeTwoCore, inf_comm] using
      distanceTwo_edgeCore_isSylow S T hTS a c ha hc hac
  obtain ⟨hOu, hindexu⟩ := criticalPair_coreIntersection_data S T hTS hP hSne hA
    u c cfg.first_shift.shifted_critical hb
  obtain ⟨hOc, hindexc⟩ := criticalPair_coreIntersection_data S T hTS hP hSne hA
    c u hinp.critical.reverse_critical hb
  rw [hOu] at hOuZa
  rw [hOc] at hOcZa
  have hIu : vertexZ S u ⊓ vertexZ S a = vertexZ S u ⊓ vertexTwoCore S c :=
    le_antisymm (inf_le_inf_left _ hZaQc) (le_inf inf_le_left hOuZa)
  have hIc : vertexZ S c ⊓ vertexZ S a = vertexZ S c ⊓ vertexTwoCore S u :=
    le_antisymm (inf_le_inf_left _ hZaQu) (le_inf inf_le_left hOcZa)
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.inf_relIndex_left (vertexZ S u) (vertexZ S a), hIu]
    exact hindexu
  · rw [← Subgroup.inf_relIndex_left (vertexZ S c) (vertexZ S a), hIc]
    exact hindexc
  · apply le_trans hinp.critical.commutator_le_inf
    apply le_trans (inf_le_inf_left _ ?_) hOuZa
    intro z hz
    exact (mem_omegaOneCenterAmbient_iff _ z).mp (hinp.right_Z_le_coreOmega hz) |>.1

private theorem central_and_noncomm
    (S : Subgroup M) (a a' c u v : Vertex S)
    (hi : DistanceFour.InitialRelations S a a' c u v) :
    (vertexZ S a).subgroupOf (DistanceFour.U S a c u) ≤
      Subgroup.center (DistanceFour.U S a c u) ∧
    _root_.commutator (DistanceFour.U S a c u) ≠ ⊥ := by
  let U := DistanceFour.U S a c u
  constructor
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (hi.Z_centralizes_U z hz w w.property).symm
  · intro hcomm
    let _ : IsMulCommutative U := (commutator_eq_bot_iff U).mp hcomm
    apply hi.Y_ne_bot
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hzU : z ∈ U := (show vertexZ S u ≤ U from le_sup_right) hz
    have hwU : w ∈ U := (show vertexZ S c ≤ U from le_sup_right.trans le_sup_left) hw
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm
      (⟨w, hwU⟩ : U) ⟨z, hzU⟩)

private theorem vertexZ_elementary_from_module [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (hV : IsElementaryAbelian 2 (vertexModule S a)) :
    IsElementaryAbelian 2 (vertexZ S a) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  have hmap : (vertexModule S a).map (stabilizer S a).subtype = vertexZ S a :=
    vertexZ_eq_local_vSubgroup S a
  rw [← hmap]
  exact IsElementaryAbelian.map_subtype

private theorem quotient_data [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v)
    [((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).Normal] :
    ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).index ≤ 4 ∧
    IsElementaryAbelian 2 ((DistanceFour.U S a c u) ⧸
      (vertexZ S a).subgroupOf (DistanceFour.U S a c u)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 0 < criticalDistance S := by omega
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  obtain ⟨hindexu, hindexc, hY⟩ := intersection_data S T hTS hP hSne hA a a' c u v hb4 cfg
  obtain ⟨hVu, _, hinp⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c cfg.first_shift.shifted_critical hb
  obtain ⟨hVc, _, _⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    c u hinp.critical.reverse_critical hb
  let U := DistanceFour.U S a c u
  let Z := (vertexZ S a).subgroupOf U
  let B := (vertexZ S c).subgroupOf U
  let C := (vertexZ S u).subgroupOf U
  have haU : vertexZ S a ≤ U := le_sup_left.trans le_sup_left
  have hcU : vertexZ S c ≤ U := le_sup_right.trans le_sup_left
  have huU : vertexZ S u ≤ U := le_sup_right
  have hUG : U ≤ stabilizer S a := hi.U_le_core.trans (Subgroup.map_subtype_le _)
  let _ : Finite U := Finite.of_injective (Subgroup.inclusion hUG)
    (Subgroup.inclusion_injective hUG)
  let _ : IsElementaryAbelian 2 (vertexZ S c) :=
    vertexZ_elementary_from_module S c hVc
  let _ : IsElementaryAbelian 2 (vertexZ S u) :=
    vertexZ_elementary_from_module S u hVu
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hcU
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf huU
  have hgen : Z ⊔ B ⊔ C = ⊤ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le haU,
      Subgroup.map_subgroupOf_eq_of_le hcU,
      Subgroup.map_subgroupOf_eq_of_le huU,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomm : ⁅B, C⁆ ≤ Z := by
    apply (Subgroup.map_le_map_iff_of_injective U.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hcU,
      Subgroup.map_subgroupOf_eq_of_le huU, Subgroup.map_subgroupOf_eq_of_le haU,
      Subgroup.commutator_comm]
    exact hY
  have hB : (B ⊓ Z).relIndex B = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_subgroupOf hcU).trans hindexc
  have hC : (C ⊓ Z).relIndex C = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_subgroupOf huU).trans hindexu
  exact Subgroup.central_two_factor_quotient Z B C hgen hcomm hB hC

public theorem distanceFour_center_and_index [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v) :
    Subgroup.center (DistanceFour.U S a c u) =
      (vertexZ S a).subgroupOf (DistanceFour.U S a c u) ∧
    ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).index = 4 := by
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  obtain ⟨hZ, hnoncomm⟩ := central_and_noncomm S a a' c u v hi
  let U := DistanceFour.U S a c u
  let Z := (vertexZ S a).subgroupOf U
  have hUG : U ≤ stabilizer S a := hi.U_le_core.trans (Subgroup.map_subtype_le _)
  let _ : Finite U := Finite.of_injective (Subgroup.inclusion hUG)
    (Subgroup.inclusion_injective hUG)
  let _ : Z.Normal := ⟨fun z hz g => by
    rw [(Subgroup.mem_center_iff.mp (hZ hz)) g, mul_inv_cancel_right]
    exact hz⟩
  have hq := quotient_data S T hTS hP hSne hA a a' c u v hb4 cfg
  exact Subgroup.center_eq_and_index_four_of_central_small_index Z hZ hq.1 hnoncomm

public theorem distanceFour_centralQuotient_elementary [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v)
    [((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).Normal] :
    IsElementaryAbelian 2 ((DistanceFour.U S a c u) ⧸
      (vertexZ S a).subgroupOf (DistanceFour.U S a c u)) :=
  (quotient_data S T hTS hP hSne hA a a' c u v hb4 cfg).2

end Stellmacher.PushingUp
