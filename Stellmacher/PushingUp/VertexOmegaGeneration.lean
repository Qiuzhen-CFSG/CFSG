module

public import Stellmacher.PushingUp.OmegaCenterGeneration
public import Stellmacher.PushingUp.ShiftSharedSylow

/-!
# Generating a vertex center from two Sylow omega centers

The principal theorem transports two-Sylow omega-center generation into the
free-amalgam graph: if ambient Sylows `P,Q` generate `G_a` and
`[Z_a,P] ≤ Ω₁ Z(P)`, then `Z_a = Ω₁ Z(P) Ω₁ Z(Q)`.

The graph subgroup is identified with the mapped normal closure of one
intrinsic Sylow omega center, using Sylow conjugacy and its defining sSup.
The finite intrinsic generation theorem then transports through the injective
stabilizer inclusion. Two supporting results supply its hypotheses in the
source configuration: a length-two edge core is a Sylow at either endpoint,
and the critical-pair Sylow acts quadratically because the vertex core
centralizes `Z_a` and source (2.2)(d) contains the endpoint commutator.

Source: B. Stellmacher, *Pushing up* (1986), (2.2)--(2.3) and the omega-center
generation step of (3.3), journal pp.11--12 and 15. Only vertex stabilizers
are finite; no finite vertex-set or free-amalgam hypothesis is used.
-/

namespace Stellmacher.PushingUp
open scoped commutatorElement
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem omegaNormalClosure_map_eq_vertexZ [Finite M]
    (S : Subgroup M) (a : Vertex S) (P : Sylow 2 (stabilizer S a)) :
    (Subgroup.normalClosure
      (omegaOneCenterAmbient (P : Subgroup (stabilizer S a)) :
        Set (stabilizer S a))).map (stabilizer S a).subtype = vertexZ S a := by
  rw [omegaNormalClosure_eq_sSup_sylows]
  apply le_antisymm
  · rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun W => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hW => ?_
    obtain ⟨Q, rfl⟩ := hW
    rw [← omegaOneCenterAmbient_map_injective
      (stabilizer S a).subtype (stabilizer S a).subtype_injective]
    exact le_sSup ⟨Q, rfl⟩
  · unfold vertexZ
    rw [sSup_eq_iSup]
    refine iSup_le fun W => iSup_le fun hW => ?_
    obtain ⟨Q, rfl⟩ := hW
    change omegaOneCenterAmbient
      ((Q : Subgroup (stabilizer S a)).map (stabilizer S a).subtype) ≤ _
    rw [omegaOneCenterAmbient_map_injective
      (stabilizer S a).subtype (stabilizer S a).subtype_injective]
    exact Subgroup.map_mono (le_sSup ⟨Q, rfl⟩)

private theorem common_neighbor_for_omega
    (S : Subgroup M) {x y : Vertex S}
    (hxy : (cosetGraph S).dist x y = 2) :
    ∃ d : Vertex S, Adjacent S x d ∧ Adjacent S d y := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist x y
  have hpnon : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp, hxy]
    omega
  refine ⟨p.penultimate, ?_, ?_⟩
  · have hdist : (cosetGraph S).dist x p.penultimate = 1 := by
      have hdrop := SimpleGraph.length_eq_dist_of_subwalk hp
        ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
      rw [SimpleGraph.Walk.length_dropLast, hp, hxy] at hdrop
      omega
    exact (cosetGraph_adj S x p.penultimate).1
      (SimpleGraph.dist_eq_one_iff_adj.mp hdist)
  · exact (cosetGraph_adj S p.penultimate y).1 (p.adj_penultimate hpnon)

public theorem distanceTwo_edgeCore_isSylow [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x y : Vertex S) (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hxy : (cosetGraph S).dist x y = 2) :
    IsSylowSubgroupIn (edgeTwoCore S y x) (stabilizer S x) := by
  obtain ⟨d, hxd, hdy⟩ := common_neighbor_for_omega S hxy
  have hne : x ≠ y := by
    intro h
    subst y
    simp at hxy
  rw [edgeTwoCore_distanceTwo S T hTS x d y hx hy hxd hdy hne,
    incident_edgeTwoCore_eq_edgeStabilizer S T hTS x d hx hxd]
  exact incident_edgeStabilizer_isSylow S T hTS x d hx hxd

public theorem vertexZ_eq_sup_omega_of_generating_sylows [Finite M]
    (S : Subgroup M) (a : Vertex S) (P Q : Subgroup (FreeAmalgam S))
    (hP : IsSylowSubgroupIn P (stabilizer S a))
    (hQ : IsSylowSubgroupIn Q (stabilizer S a))
    (hgen : P ⊔ Q = stabilizer S a)
    (hcomm : ⁅vertexZ S a, P⁆ ≤ omegaOneCenterAmbient P) :
    vertexZ S a = omegaOneCenterAmbient P ⊔ omegaOneCenterAmbient Q := by
  obtain ⟨PI, hPI⟩ := hP
  obtain ⟨QI, hQI⟩ := hQ
  let G := stabilizer S a
  let V : Subgroup G := Subgroup.normalClosure
    (omegaOneCenterAmbient (PI : Subgroup G) : Set G)
  have hVmap : V.map G.subtype = vertexZ S a :=
    omegaNormalClosure_map_eq_vertexZ S a PI
  have hgenI : (PI : Subgroup G) ⊔ (QI : Subgroup G) = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, hPI, hQI, hgen]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcommI : ⁅V, (PI : Subgroup G)⁆ ≤
      omegaOneCenterAmbient (PI : Subgroup G) := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [Subgroup.map_commutator, hVmap, hPI,
      ← omegaOneCenterAmbient_map_injective G.subtype G.subtype_injective, hPI]
    exact hcomm
  have hI := omegaNormalClosure_eq_sup_of_generating_sylows PI QI hgenI hcommI
  have h := congrArg (Subgroup.map G.subtype) hI
  rw [hVmap, Subgroup.map_sup,
    ← omegaOneCenterAmbient_map_injective G.subtype G.subtype_injective,
    ← omegaOneCenterAmbient_map_injective G.subtype G.subtype_injective,
    hPI, hQI] at h
  exact h


private theorem commutator_sup_core_le
    {G : Type*} [Group G] (V A Q C : Subgroup G) [Q.Normal]
    (hVA : ⁅V, A⁆ ≤ C) (hVQ : V ≤ Subgroup.centralizer Q) :
    ⁅V, A ⊔ Q⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hvq : ⁅v, q⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_centralizer_iff.mp (hVQ hv)) q hq).symm
  rw [commutatorElement_mul_right_eq_mul_conj, hvq]
  simpa using (Subgroup.commutator_le.mp hVA) v hv a ha

public theorem criticalPair_sourceSylow_quadratic_ambient [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S) :
    ⁅vertexZ S a, vertexZ S a' ⊔ vertexTwoCore S a⁆ ≤
      omegaOneCenterAmbient (vertexZ S a' ⊔ vertexTwoCore S a) := by
  obtain ⟨hW, ha', hinputs⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    a a' hcrit hb
  obtain ⟨_, _, h22⟩ := criticalPair_sl2Two S T hTS hP hSne hA a a' hcrit hb
  let G := stabilizer S a
  let V : Subgroup G := (vertexZ S a).subgroupOf G
  let A : Subgroup G := (vertexZ S a').subgroupOf G
  let Q : Subgroup G := pCore 2 G
  let C : Subgroup G := (⁅vertexZ S a, vertexZ S a'⁆).subgroupOf G
  have hVG : vertexZ S a ≤ G := vertexZ_le_stabilizer S a
  have hCG : ⁅vertexZ S a, vertexZ S a'⁆ ≤ G :=
    hinputs.critical.commutator_le_inf.trans inf_le_left |>.trans hVG
  have hVA : ⁅V, A⁆ ≤ C := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hVG,
      Subgroup.map_subgroupOf_eq_of_le ha',
      Subgroup.map_subgroupOf_eq_of_le hCG]
  have hVQ : V ≤ Subgroup.centralizer Q := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    exact (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) (v : FreeAmalgam S)).mp
      (hinputs.left_Z_le_coreOmega hv) |>.2.2 q ⟨q, hq, rfl⟩
  have hcomm := Subgroup.map_mono
    (commutator_sup_core_le V A Q C hVA hVQ) (f := G.subtype)
  rw [Subgroup.map_commutator, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hVG,
    Subgroup.map_subgroupOf_eq_of_le ha',
    Subgroup.map_subgroupOf_eq_of_le hCG] at hcomm
  change ⁅vertexZ S a, vertexZ S a' ⊔ vertexTwoCore S a⁆ ≤
    ⁅vertexZ S a, vertexZ S a'⁆ at hcomm
  apply hcomm.trans
  rw [h22.sourceOmegaCenter]
  exact le_sup_left

end Stellmacher.PushingUp
