module

public import Stellmacher.PushingUp.DistanceTwoShift

/-!
# The common Sylow subgroup in a distance-two shift

This module proves the common Sylow identity used in Stellmacher, *Pushing
up* (1986), (2.4)(1) and (3.3), from (2.3), assuming `2 < b`. Strict-distance
minimality puts the shifted endpoint center in the edge core; the shared
neighbor puts both vertex cores there. The Sylow conclusion of shifted
(2.2) forces equality. The two conclusions support both the upper bound on critical distance and
the distance-four contradiction. No finite vertex or finite amalgam
assumption is used.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem shared_exists_common_neighbor_of_dist_two [Finite M]
    (S : Subgroup M) {x y : Vertex S}
    (hxy : (cosetGraph S).dist x y = 2) :
    ∃ d : Vertex S, Adjacent S x d ∧ Adjacent S d y := by
  obtain ⟨p, hp⟩ :=
    (cosetGraph_connected S).exists_walk_length_eq_dist x y
  have hpnon : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp, hxy]
    omega
  refine ⟨p.penultimate, ?_, ?_⟩
  · have hdist : (cosetGraph S).dist x p.penultimate = 1 := by
      have hdrop : p.dropLast.length =
          (cosetGraph S).dist x p.penultimate :=
        SimpleGraph.length_eq_dist_of_subwalk hp
          ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
      rw [← hdrop, SimpleGraph.Walk.length_dropLast, hp, hxy]
    exact (cosetGraph_adj S x p.penultimate).1
      (SimpleGraph.dist_eq_one_iff_adj.mp hdist)
  · exact (cosetGraph_adj S p.penultimate y).1
      (p.adj_penultimate hpnon)

private theorem shared_sylowSubgroupIn_le
    {G : Type*} [Group G] {P K : Subgroup G}
    (h : IsSylowSubgroupIn P K) : P ≤ K := by
  obtain ⟨T, hT⟩ := h
  rw [← hT]
  exact Subgroup.map_subtype_le _

private theorem shared_edgeTwoCore_isPGroup
    {G : Type*} [Group G] (A B : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient (A ⊓ B)) := by
  unfold twoCoreAmbient
  exact (pCore_isPGroup (p := 2) (G := ↥(A ⊓ B))).map
    (A ⊓ B : Subgroup G).subtype

private theorem shared_le_particular_sylow_of_source_le
    {G : Type u} [Group G] [Finite G]
    (A V : Subgroup G) (P : Sylow 2 G)
    (hV : IsPGroup 2 V) (hAV : A ≤ V)
    (hsource : A ⊔ pCore 2 G = (P : Subgroup G)) :
    V ≤ (P : Subgroup G) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := pCore 2 G
  let H : Subgroup G := V ⊔ Q
  have hQnormal : Q.Normal := pCore_normal
  let _ : Q.Normal := hQnormal
  have hsup : IsPGroup 2 H :=
    hV.to_sup_of_normal_right (pCore_isPGroup (p := 2) (G := G))
  have hP_sup : (P : Subgroup G) ≤ H := by
    rw [← hsource]
    exact sup_le (hAV.trans le_sup_left) le_sup_right
  have heq : H = (P : Subgroup G) :=
    P.is_maximal' hsup hP_sup
  exact le_sup_left.trans (le_of_eq heq)

private theorem shared_le_reverse_sourceSylow
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (V : Subgroup (FreeAmalgam S))
    (hVG : V ≤ stabilizer S a')
    (hVp : IsPGroup 2 V)
    (hZaV : vertexZ S a ≤ V)
    (hsource : IsSylowSubgroupIn
      (vertexZ S a ⊔ vertexTwoCore S a') (stabilizer S a')) :
    V ≤ vertexZ S a ⊔ vertexTwoCore S a' := by
  let G := stabilizer S a'
  let A : Subgroup G := (vertexZ S a).subgroupOf G
  let V' : Subgroup G := V.subgroupOf G
  have hV'p : IsPGroup 2 V' :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVG).symm
  have hAV' : A ≤ V' := by
    intro x hx
    exact hZaV hx
  obtain ⟨P, hP⟩ := hsource
  have hsource' : A ⊔ pCore 2 G = (P : Subgroup G) := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, hP]
    rw [Subgroup.map_subgroupOf_eq_of_le (hZaV.trans hVG)]
    rfl
  have hV'P : V' ≤ (P : Subgroup G) :=
    shared_le_particular_sylow_of_source_le A V' P hV'p hAV' hsource'
  intro x hx
  rw [← hP]
  exact ⟨⟨x, hVG hx⟩, hV'P hx, rfl⟩

public theorem distanceTwoShift_sharedSylow [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (htwo : 2 < criticalDistance S)
    (hframe : DistanceTwoShift.Frame S a a' c)
    (hshift : DistanceTwoShift.Conclusion S a a' c u) :
    vertexTwoCore S a ≤ vertexZ S c ⊔ vertexTwoCore S u ∧
      edgeTwoCore S u a = vertexZ S c ⊔ vertexTwoCore S u := by
  have hb : 0 < criticalDistance S := by omega
  have hu : InMVertexOrbit S u := hshift.shifted_critical.1
  have hc : InMVertexOrbit S c :=
    (criticalPair_path T hTS hP hSne u c hshift.shifted_critical hb)
      |>.opposite_inMVertexOrbit
  obtain ⟨d, had, hdu⟩ :=
    shared_exists_common_neighbor_of_dist_two S hshift.distance_two
  have hau : a ≠ u := by
    intro hau
    subst u
    have hdist := hshift.distance_two
    simp at hdist
  have hEeq : edgeTwoCore S u a = edgeTwoCore S a d :=
    edgeTwoCore_distanceTwo S T hTS a d u hcrit.1 hu had hdu hau
  let E := edgeTwoCore S a d
  have hlocalA := criticalDistance_basic S T hTS hP hSne a d hcrit.1 had
  have hlocalU :=
    criticalDistance_basic S T hTS hP hSne u d hu (adjacent_symm S hdu)
  have hQaKa : vertexTwoCore S a ≤ neighborhoodKernel S a :=
    shared_sylowSubgroupIn_le hlocalA.twoCore_sylow_kernel
  have hQaE : vertexTwoCore S a ≤ E := by
    rw [show E = stabilizer S a ⊓ stabilizer S d from
      incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d hcrit.1 had]
    intro x hx
    have hxK := hQaKa hx
    exact ⟨hxK.1, hxK.2 d had⟩
  have hZcKa : vertexZ S c ≤ neighborhoodKernel S a := by
    apply vertexZ_le_neighborhoodKernel_of_dist_lt S hc
    rw [SimpleGraph.dist_comm]
    have hleft := hframe.left_length
    omega
  have hZcE : vertexZ S c ≤ E := hZcKa.trans (by
    rw [show E = stabilizer S a ⊓ stabilizer S d from
      incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d hcrit.1 had]
    intro x hx
    exact ⟨hx.1, hx.2 d had⟩)
  have hQuKu : vertexTwoCore S u ≤ neighborhoodKernel S u :=
    shared_sylowSubgroupIn_le hlocalU.twoCore_sylow_kernel
  have hQuEdgeUD : vertexTwoCore S u ≤ edgeTwoCore S u d := by
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS u d hu
      (adjacent_symm S hdu)]
    intro x hx
    have hxK := hQuKu hx
    exact ⟨hxK.1, hxK.2 d (adjacent_symm S hdu)⟩
  have hEdgeUDKd : edgeTwoCore S u d ≤ neighborhoodKernel S d :=
    (localKernel_at_mEdge S T hTS u d hu (adjacent_symm S hdu)).2.2.2
  have hQuE : vertexTwoCore S u ≤ E := by
    rw [show E = stabilizer S a ⊓ stabilizer S d from
      incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d hcrit.1 had]
    intro x hx
    have hxKd := hEdgeUDKd (hQuEdgeUD hx)
    exact ⟨hxKd.2 a (adjacent_symm S had), hxKd.1⟩
  have hEGa : E ≤ stabilizer S a :=
    (show E ≤ stabilizer S a ⊓ stabilizer S d by
      rw [show E = stabilizer S a ⊓ stabilizer S d from
        incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d hcrit.1 had])
      |>.trans inf_le_left
  have hEGu : E ≤ stabilizer S u := by
    intro x hx
    exact (hlocalA.edgeCore_le_neighbor_kernel hx).2 u hdu
  have hEp : IsPGroup 2 E :=
    shared_edgeTwoCore_isPGroup (stabilizer S a) (stabilizer S d)
  obtain ⟨_hWu, _hcGu, hshift22⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA u c
      hshift.shifted_critical hb
  have hPE : vertexZ S c ⊔ vertexTwoCore S u ≤ E :=
    sup_le hZcE hQuE
  have hEP : E ≤ vertexZ S c ⊔ vertexTwoCore S u :=
    shared_le_reverse_sourceSylow S c u E hEGu hEp hZcE
      hshift22.sourceSylow
  have hPEeq : vertexZ S c ⊔ vertexTwoCore S u = E :=
    le_antisymm hPE hEP
  have hQaP : vertexTwoCore S a ≤
      vertexZ S c ⊔ vertexTwoCore S u := by
    rw [hPEeq]
    exact hQaE
  exact ⟨hQaP, hEeq.trans hPEeq.symm⟩

end Stellmacher.PushingUp
