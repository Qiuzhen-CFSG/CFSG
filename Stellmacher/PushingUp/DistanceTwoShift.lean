module

public import Stellmacher.PushingUp.GeneratingPredecessor
public import Stellmacher.PushingUp.DistanceTwoCore
public import Stellmacher.PushingUp.NeighborCenterClosure

/-!
# Shifting a critical pair by two vertices

This module proves the distance-two shift in Stellmacher, *Pushing up*, Arch.
Math. 46 (1986), proof of (2.3), journal p.12.  Given a critical pair
`(a,a')` and a vertex `a'-2` at the audited distances from its endpoints, it
constructs a neighbor `a-2` two steps from `a`.  Its center escapes
`G_(a'-2) ∩ G_(a')`, the shifted pair `(a-2,a'-2)` is critical, its
length-two edge core together with `Z_(a')` generates `G_a`, and for critical
distance greater than two the shifted endpoint commutator lies in `Z(G_a)`.

The proof first uses `criticalPair_generatingPredecessor` and
`neighborCenterClosure`.  If every neighbor center lay in `G_(a')`, reverse
(2.2)(a) and (1.4)(b) would make their closure normal in both stabilizers of
an edge, contradicting the faithful-amalgam normality obstruction.  The
escaping neighbor gives shifted criticality by critical-distance minimality,
parity, and a distance-two local-kernel bridge.  The accepted
`edgeTwoCore_distanceTwo` identity transports the generation equation.
Finally, shifted (2.2)(d) identifies the relevant Sylow omega center on the
edge core; strict distance places the other commutator factor in
`O_2(G_(a'))`, so the two displayed generators centralize the commutator.

The source frame, its five-clause conclusion, and the principal shift theorem
form the main public boundary. Two source adapters also expose the reverse
Sylow-containment and closure-commutator bounds for the later shifted-normality
argument. Critical-distance transport and arbitrary-edge obstruction helpers
remain private.
No finiteness of the vertex set or free amalgam is assumed, and the proof uses
no native decision procedure.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open scoped commutatorElement
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

namespace DistanceTwoShift

public structure Frame {M : Type u} [Group M] (S : Subgroup M)
    (a a' aPrimeMinusTwo : Vertex S) : Prop where
  left_length :
    (cosetGraph S).dist a aPrimeMinusTwo + 2 = criticalDistance S
  right_length : (cosetGraph S).dist aPrimeMinusTwo a' = 2

public structure Conclusion {M : Type u} [Group M] (S : Subgroup M)
    (a a' aPrimeMinusTwo aMinusTwo : Vertex S) : Prop where
  distance_two : (cosetGraph S).dist a aMinusTwo = 2
  escapes_endpoint_intersection :
    ¬ vertexZ S aMinusTwo ≤
      stabilizer S aPrimeMinusTwo ⊓ stabilizer S a'
  shifted_critical : IsCriticalPair S aMinusTwo aPrimeMinusTwo
  generates_left_stabilizer :
    edgeTwoCore S aMinusTwo a ⊔ vertexZ S a' = stabilizer S a
  commutator_central_of_two_lt :
    2 < criticalDistance S →
      ⁅vertexZ S aMinusTwo, vertexZ S aPrimeMinusTwo⁆ ≤
        (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype

end DistanceTwoShift

private theorem le_particular_sylow_of_source_le
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

/-- A 2-subgroup containing the opposite vertex center lies in its prescribed
Sylow supplement of the local two-core. -/
public theorem le_reverse_sourceSylow
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
    le_particular_sylow_of_source_le A V' P hV'p hAV' hsource'
  intro x hx
  rw [← hP]
  exact ⟨⟨x, hVG hx⟩, hV'P hx, rfl⟩

private theorem commutator_le_left_of_le_sup_of_normal_right
    {G : Type*} [Group G]
    (A Q V B : Subgroup G) [Q.Normal]
    (hV : V ≤ A ⊔ Q) (hAB : ⁅A, B⁆ ≤ A)
    (hBQ : B ≤ Subgroup.centralizer Q) :
    ⁅V, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro v hv b hb
  obtain ⟨a, ha, q, hq, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (hV hv)
  have hab : ⁅a, b⁆ ∈ A :=
    (Subgroup.commutator_le.mp hAB) a ha b hb
  have hqb : q * b = b * q :=
    (Subgroup.mem_centralizer_iff.mp (hBQ hb)) q hq
  simpa [commutatorElement_def, hqb, mul_assoc] using hab

/-- A subgroup in the opposite-center/core supplement has its commutator with
the local vertex center contained in that opposite center. -/
public theorem neighborClosure_commutator_le
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (V : Subgroup (FreeAmalgam S))
    (hVG : V ≤ stabilizer S a')
    (hVsource : V ≤ vertexZ S a ⊔ vertexTwoCore S a')
    {hW : IsElementaryAbelian 2 (vertexModule S a)}
    {ha' : vertexZ S a' ≤ stabilizer S a}
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hW) :
    ⁅V, vertexZ S a'⁆ ≤ vertexZ S a := by
  let G := stabilizer S a'
  let A : Subgroup G := (vertexZ S a).subgroupOf G
  let Q : Subgroup G := pCore 2 G
  let VI : Subgroup G := V.subgroupOf G
  let B : Subgroup G := (vertexZ S a').subgroupOf G
  have hVIle : VI ≤ A ⊔ Q := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hVG, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hinputs.left_Z_le_right_stabilizer]
    exact hVsource
  have hAB : ⁅A, B⁆ ≤ A := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hinputs.left_Z_le_right_stabilizer,
      Subgroup.map_subgroupOf_eq_of_le (vertexZ_le_stabilizer S a')]
    exact hinputs.critical.commutator_le_inf.trans inf_le_left
  have hBQ : B ≤ Subgroup.centralizer Q := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply G.subtype_injective
    have hq' : (q : FreeAmalgam S) ∈ vertexTwoCore S a' := ⟨q, hq, rfl⟩
    exact (mem_omegaOneCenterAmbient_iff
      (vertexTwoCore S a') (b : FreeAmalgam S)).mp
        (hinputs.right_Z_le_coreOmega hb) |>.2.2 (q : FreeAmalgam S) hq'
  have hinter : ⁅VI, B⁆ ≤ A :=
    commutator_le_left_of_le_sup_of_normal_right A Q VI B hVIle hAB hBQ
  have hmap : (⁅VI, B⁆).map G.subtype ≤ A.map G.subtype :=
    Subgroup.map_mono hinter
  rw [Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hVG,
    Subgroup.map_subgroupOf_eq_of_le (vertexZ_le_stabilizer S a'),
    Subgroup.map_subgroupOf_eq_of_le hinputs.left_Z_le_right_stabilizer] at hmap
  exact hmap

private theorem edgeTwoCore_le_inf (S : Subgroup M) (a d : Vertex S) :
    edgeTwoCore S a d ≤ stabilizer S a ⊓ stabilizer S d := by
  exact Subgroup.map_subtype_le _

private theorem neighbor_inMVertexOrbit_of_commonNeighbor [Finite M]
    (S : Subgroup M) {a d u : Vertex S}
    (ha : InMVertexOrbit S a) (had : Adjacent S a d)
    (hdu : Adjacent S d u) : InMVertexOrbit S u := by
  obtain ⟨g, _hg, hgu⟩ := stabilizer_transitive_neighbors S d
    (adjacent_symm S had) hdu
  obtain ⟨x, hxa⟩ := ha
  refine ⟨x * g, ?_⟩
  rw [act_mul, ← hxa]
  exact hgu.symm

private theorem inMVertexOrbit_color_false
    (S : Subgroup M) {a : Vertex S} (ha : InMVertexOrbit S a) :
    color S a = false := by
  obtain ⟨g, rfl⟩ := ha
  rw [action_preserves_color]
  rfl

private theorem dist_two_of_commonNeighbor [Finite M]
    (S : Subgroup M) {a d u : Vertex S}
    (ha : InMVertexOrbit S a) (hu : InMVertexOrbit S u)
    (had : Adjacent S a d) (hdu : Adjacent S d u)
    (hau : a ≠ u) : (cosetGraph S).dist a u = 2 := by
  have hadDist : (cosetGraph S).dist a d = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj S a d).2 had)
  have hduDist : (cosetGraph S).dist d u = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj S d u).2 hdu)
  have hle : (cosetGraph S).dist a u ≤ 2 := by
    have htri := (cosetGraph_connected S).dist_triangle
      (u := a) (v := d) (w := u)
    omega
  have hzero : (cosetGraph S).dist a u ≠ 0 := by
    intro hzero
    exact hau ((cosetGraph_connected S).dist_eq_zero_iff.mp hzero)
  have hone : (cosetGraph S).dist a u ≠ 1 := by
    intro hone
    have hadj : Adjacent S a u :=
      (cosetGraph_adj S a u).1 (SimpleGraph.dist_eq_one_iff_adj.mp hone)
    exact adjacent_color_ne S hadj (by
      rw [inMVertexOrbit_color_false S ha,
        inMVertexOrbit_color_false S hu])
  omega

private theorem exists_common_neighbor_of_dist_two [Finite M]
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

private theorem neighborhoodKernel_le_stabilizer_of_dist_two [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S) {x y : Vertex S}
    (hx : InMVertexOrbit S x)
    (hxy : (cosetGraph S).dist x y = 2) :
    neighborhoodKernel S x ≤ stabilizer S y := by
  obtain ⟨d, hxd, hdy⟩ := exists_common_neighbor_of_dist_two S hxy
  have hKedge : neighborhoodKernel S x ≤ edgeTwoCore S x d := by
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS x d hx hxd]
    intro g hg
    exact ⟨hg.1, hg.2 d hxd⟩
  have hEkernel : edgeTwoCore S x d ≤ neighborhoodKernel S d :=
    (localKernel_at_mEdge S T hTS x d hx hxd).2.2.2
  intro g hg
  exact (hEkernel (hKedge hg)).2 y hdy

private def pathActEquiv (S : Subgroup M) (g : FreeAmalgam S) :
    Vertex S ≃ Vertex S where
  toFun := act S g
  invFun := act S g⁻¹
  left_inv := fun d => by rw [← act_mul]; simp
  right_inv := fun d => by rw [← act_mul]; simp

private def pathActIso (S : Subgroup M) (g : FreeAmalgam S) :
    cosetGraph S ≃g cosetGraph S :=
  RelIso.mk (pathActEquiv S g) (fun {d e} => by
    change (cosetGraph S).Adj (act S g d) (act S g e) ↔
      (cosetGraph S).Adj d e
    rw [cosetGraph_adj, cosetGraph_adj]
    exact adjacent_act_iff S g d e)

private theorem path_dist_act (S : Subgroup M) (g : FreeAmalgam S)
    (d e : Vertex S) :
    (cosetGraph S).dist (act S g d) (act S g e) =
      (cosetGraph S).dist d e := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist d e
    calc
      (cosetGraph S).dist (act S g d) (act S g e) ≤
          (p.map (pathActIso S g).toRelEmbedding.toRelHom).length :=
        SimpleGraph.dist_le _
      _ = p.length := SimpleGraph.Walk.length_map _ _
      _ = (cosetGraph S).dist d e := hp
  · obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist
      (act S g d) (act S g e)
    have hle : (cosetGraph S).dist
        (act S g⁻¹ (act S g d)) (act S g⁻¹ (act S g e)) ≤
        (cosetGraph S).dist (act S g d) (act S g e) := by
      calc
        (cosetGraph S).dist
            (act S g⁻¹ (act S g d)) (act S g⁻¹ (act S g e)) ≤
            (p.map (pathActIso S g⁻¹).toRelEmbedding.toRelHom).length :=
          SimpleGraph.dist_le _
        _ = p.length := SimpleGraph.Walk.length_map _ _
        _ = (cosetGraph S).dist (act S g d) (act S g e) := hp
    simpa [← act_mul] using hle

private theorem path_neighborhoodKernel_act (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    neighborhoodKernel S (act S g d) =
      (neighborhoodKernel S d).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext h
  constructor
  · intro hh
    refine ⟨g * h * g⁻¹, ?_, by simp [mul_assoc]⟩
    change g * h * g⁻¹ ∈ stabilizer S d ∧
      ∀ e : Vertex S, Adjacent S d e → g * h * g⁻¹ ∈ stabilizer S e
    constructor
    · change act S (g * h * g⁻¹) d = d
      calc
        act S (g * h * g⁻¹) d =
            act S g⁻¹ (act S h (act S g d)) := by
          simp only [act_mul, mul_assoc]
        _ = act S g⁻¹ (act S g d) := congrArg (act S g⁻¹) hh.1
        _ = d := by rw [← act_mul]; simp
    · intro f hdf
      have hhf := hh.2 (act S g f) ((adjacent_act_iff S g d f).2 hdf)
      change act S (g * h * g⁻¹) f = f
      calc
        act S (g * h * g⁻¹) f =
            act S g⁻¹ (act S h (act S g f)) := by
          simp only [act_mul, mul_assoc]
        _ = act S g⁻¹ (act S g f) := congrArg (act S g⁻¹) hhf
        _ = f := by rw [← act_mul]; simp
  · rintro ⟨k, hk, rfl⟩
    change k ∈ stabilizer S d ∧
      ∀ e : Vertex S, Adjacent S d e → k ∈ stabilizer S e at hk
    change (MulAut.conj g⁻¹) k ∈ stabilizer S (act S g d) ∧
      ∀ e : Vertex S, Adjacent S (act S g d) e →
        (MulAut.conj g⁻¹) k ∈ stabilizer S e
    constructor
    · rw [stabilizer_act]
      exact ⟨k, hk.1, rfl⟩
    · intro f hf
      let e := act S g⁻¹ f
      have he : Adjacent S d e := by
        have h := (adjacent_act_iff S g⁻¹ (act S g d) f).2 hf
        simpa [e, ← act_mul] using h
      have hfe : act S g e = f := by
        dsimp [e]
        rw [← act_mul]
        simp
      rw [← hfe, stabilizer_act]
      exact ⟨k, hk.2 e he, rfl⟩

private noncomputable def pathSylowOmegaJoin
    {G : Type*} [Group G] (P : Subgroup G) : Subgroup G :=
  sSup {Z : Subgroup G | ∃ T : Sylow 2 P,
    Z = omegaOneCenterAmbient ((T : Subgroup P).map P.subtype)}

private theorem pathSylowAmbient_map_equiv
    {G G' : Type*} [Group G] [Group G'] (f : G ≃* G')
    (P : Subgroup G) [Finite P] (T : Sylow 2 P) :
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    let T' : Sylow 2 (P.map f.toMonoidHom) := T.mapSurjective hfP
    ((T' : Subgroup (P.map f.toMonoidHom)).map
        (P.map f.toMonoidHom).subtype) =
      (((T : Subgroup P).map P.subtype).map f.toMonoidHom) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  change (((T : Subgroup P).map _).map _) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem pathSylowOmegaJoin_map_equiv
    {G G' : Type*} [Group G] [Group G'] (f : G ≃* G')
    (P : Subgroup G) [Finite P] :
    pathSylowOmegaJoin (P.map f.toMonoidHom) =
      (pathSylowOmegaJoin P).map f.toMonoidHom := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · unfold pathSylowOmegaJoin
    rw [sSup_eq_iSup]
    refine iSup_le fun W ↦ ?_
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T', rfl⟩
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hfP 2 T'
    rw [← hT, pathSylowAmbient_map_equiv,
      omegaOneCenterAmbient_map_injective f.toMonoidHom f.injective]
    exact Subgroup.map_mono (le_sSup ⟨T, rfl⟩)
  · unfold pathSylowOmegaJoin
    rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun W ↦ ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T, rfl⟩
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    let T' : Sylow 2 (P.map f.toMonoidHom) := T.mapSurjective hfP
    rw [← omegaOneCenterAmbient_map_injective f.toMonoidHom f.injective,
      ← pathSylowAmbient_map_equiv]
    exact le_sSup ⟨T', rfl⟩

private theorem vertexZ_act [Finite M] (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    vertexZ S (act S g d) =
      (vertexZ S d).map (MulAut.conj g⁻¹).toMonoidHom := by
  change pathSylowOmegaJoin (stabilizer S (act S g d)) =
    (pathSylowOmegaJoin (stabilizer S d)).map
      (MulAut.conj g⁻¹).toMonoidHom
  rw [stabilizer_act]
  exact pathSylowOmegaJoin_map_equiv (MulAut.conj g⁻¹) (stabilizer S d)

private theorem criticalDistance_le_of_escape [Finite M]
    (S : Subgroup M) {a d : Vertex S} (ha : InMVertexOrbit S a)
    (hnot : ¬ vertexZ S a ≤ neighborhoodKernel S d) :
    criticalDistance S ≤ (cosetGraph S).dist a d := by
  obtain ⟨g, rfl⟩ := ha
  let d₀ := act S g⁻¹ d
  have hd : act S g d₀ = d := by
    dsimp [d₀]
    rw [← act_mul]
    simp
  apply Nat.sInf_le
  refine ⟨d₀, ?_, ?_⟩
  · rw [← path_dist_act S g, hd]
  · intro hle
    have hmap : (vertexZ S (mVertex S 1)).map
          (MulAut.conj g⁻¹).toMonoidHom ≤
        (neighborhoodKernel S d₀).map
          (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hle
    rw [← vertexZ_act S g (mVertex S 1),
      ← path_neighborhoodKernel_act S g d₀, hd] at hmap
    exact hnot hmap

private theorem vertexZ_le_kernel_of_dist_lt [Finite M]
    (S : Subgroup M) {a d : Vertex S} (ha : InMVertexOrbit S a)
    (hlt : (cosetGraph S).dist a d < criticalDistance S) :
    vertexZ S a ≤ neighborhoodKernel S d := by
  by_contra hnot
  exact (not_le_of_gt hlt) (criticalDistance_le_of_escape S ha hnot)

private theorem sylowSubgroupIn_le
    {G : Type*} [Group G] {P K : Subgroup G}
    (h : IsSylowSubgroupIn P K) : P ≤ K := by
  obtain ⟨T, hT⟩ := h
  rw [← hT]
  exact Subgroup.map_subtype_le _

private theorem edgeTwoCore_isPGroup
    {G : Type*} [Group G] (A B : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient (A ⊓ B)) := by
  unfold twoCoreAmbient
  exact (pCore_isPGroup (p := 2) (G := ↥(A ⊓ B))).map
    (A ⊓ B : Subgroup G).subtype

private theorem vertexTwoCore_le_neighborhoodKernel [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S) {x d : Vertex S}
    (hx : InMVertexOrbit S x) (hxd : Adjacent S x d) :
    vertexTwoCore S x ≤ neighborhoodKernel S x :=
  sylowSubgroupIn_le (localKernel_at_mEdge S T hTS x d hx hxd).1

private theorem sylowSubgroupIn_eq_self_of_isPGroup
    {G : Type*} [Group G] (Q K : Subgroup G)
    (hKp : IsPGroup 2 K) (hQ : IsSylowSubgroupIn Q K) : Q = K := by
  obtain ⟨P, hPmap⟩ := hQ
  have htopP : IsPGroup 2 (⊤ : Subgroup K) := hKp.to_subgroup ⊤
  have htop : (⊤ : Subgroup K) = (P : Subgroup K) :=
    P.is_maximal' htopP le_top
  rw [← hPmap, ← htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem neighborhoodKernel_eq_vertexTwoCore [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S) {x d : Vertex S}
    (hx : InMVertexOrbit S x) (hxd : Adjacent S x d) :
    neighborhoodKernel S x = vertexTwoCore S x := by
  have hKedge : neighborhoodKernel S x ≤ edgeTwoCore S x d := by
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS x d hx hxd]
    intro g hg
    exact ⟨hg.1, hg.2 d hxd⟩
  have hKp : IsPGroup 2 (neighborhoodKernel S x) :=
    (edgeTwoCore_isPGroup (stabilizer S x) (stabilizer S d)).to_le hKedge
  exact (sylowSubgroupIn_eq_self_of_isPGroup _ _ hKp
    (localKernel_at_mEdge S T hTS x d hx hxd).1).symm

private theorem finalStrictKernelInclusions [Finite M]
    (S : Subgroup M) {a a' c : Vertex S}
    (hc : InMVertexOrbit S c)
    (hleft : (cosetGraph S).dist a c + 2 = criticalDistance S)
    (hright : (cosetGraph S).dist c a' = 2)
    (htwo : 2 < criticalDistance S) :
    vertexZ S c ≤ neighborhoodKernel S a ∧
      vertexZ S c ≤ neighborhoodKernel S a' := by
  constructor
  · apply vertexZ_le_kernel_of_dist_lt S hc
    rw [SimpleGraph.dist_comm]
    omega
  · apply vertexZ_le_kernel_of_dist_lt S hc
    rw [hright]
    exact htwo

private theorem vertexZ_le_stabilizer_of_dist_le [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) {x y : Vertex S}
    (hx : InMVertexOrbit S x)
    (hb : 0 < criticalDistance S)
    (hxy : (cosetGraph S).dist x y ≤ criticalDistance S) :
    vertexZ S x ≤ stabilizer S y := by
  by_cases hlt : (cosetGraph S).dist x y < criticalDistance S
  · intro z hz
    exact (vertexZ_le_kernel_of_dist_lt S hx hlt hz).1
  · have heq : (cosetGraph S).dist x y = criticalDistance S := by omega
    by_cases hker : vertexZ S x ≤ neighborhoodKernel S y
    · intro z hz
      exact (hker hz).1
    · exact (criticalPair_path T hTS hP hSne x y ⟨hx, heq, hker⟩ hb)
        |>.left_Z_le_right_stabilizer

private theorem walk_even_iff_color_eq (S : Subgroup M)
    {a b : Vertex S} (p : (cosetGraph S).Walk a b) :
    Even p.length ↔ color S a = color S b := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
      have hcolor : color S a ≠ color S b :=
        adjacent_color_ne S ((cosetGraph_adj S a b).1 hab)
      cases hca : color S a <;> cases hcb : color S b <;>
        cases hcc : color S c <;> simp_all

private theorem even_dist_iff_color_eq (S : Subgroup M)
    (a b : Vertex S) :
    Even ((cosetGraph S).dist a b) ↔ color S a = color S b := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist a b
  rw [← hp]
  exact walk_even_iff_color_eq S p

private theorem inMVertexOrbit_iff_color_eq_false (S : Subgroup M)
    (a : Vertex S) : InMVertexOrbit S a ↔ color S a = false := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [action_preserves_color]
    rfl
  · intro ha
    cases a with
    | inl q =>
        induction q using Quotient.inductionOn
        rename_i x
        refine ⟨x, ?_⟩
        change mVertex S x = act S x (mVertex S 1)
        simp
    | inr q => simp [color] at ha

private theorem even_dist_of_mVertexOrbits (S : Subgroup M)
    {x y : Vertex S} (hx : InMVertexOrbit S x)
    (hy : InMVertexOrbit S y) : Even ((cosetGraph S).dist x y) := by
  apply (even_dist_iff_color_eq S x y).2
  rw [(inMVertexOrbit_iff_color_eq_false S x).1 hx,
    (inMVertexOrbit_iff_color_eq_false S y).1 hy]

private theorem mVertexOrbit_of_even_dist (S : Subgroup M)
    {x y : Vertex S} (hx : InMVertexOrbit S x)
    (heven : Even ((cosetGraph S).dist x y)) : InMVertexOrbit S y := by
  apply (inMVertexOrbit_iff_color_eq_false S y).2
  have hcolor := (even_dist_iff_color_eq S x y).1 heven
  rw [(inMVertexOrbit_iff_color_eq_false S x).1 hx] at hcolor
  exact hcolor.symm

private theorem neighbor_dist_le_frame_endpoint [Finite M]
    (S : Subgroup M) {a d u c : Vertex S}
    (had : Adjacent S a d) (hdu : Adjacent S d u)
    (hframe : (cosetGraph S).dist a c + 2 = criticalDistance S) :
    (cosetGraph S).dist u c ≤ criticalDistance S := by
  have hudDist : (cosetGraph S).dist u d = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj S u d).2 (adjacent_symm S hdu))
  have hdaDist : (cosetGraph S).dist d a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj S d a).2 (adjacent_symm S had))
  have htri₁ := (cosetGraph_connected S).dist_triangle
    (u := u) (v := d) (w := a)
  have htri₂ := (cosetGraph_connected S).dist_triangle
    (u := u) (v := a) (w := c)
  omega

private theorem shiftedCritical_of_escape [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a a' c d u : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (had : Adjacent S a d) (hdu : Adjacent S d u)
    (hleft : (cosetGraph S).dist a c + 2 = criticalDistance S)
    (hright : (cosetGraph S).dist c a' = 2)
    (hZuC : vertexZ S u ≤ stabilizer S c)
    (hescape : ¬ vertexZ S u ≤ stabilizer S c ⊓ stabilizer S a') :
    IsCriticalPair S u c := by
  have hu : InMVertexOrbit S u :=
    neighbor_inMVertexOrbit_of_commonNeighbor S hcrit.1 had hdu
  have hbEven : Even (criticalDistance S) :=
    (criticalDistance_basic S T hTS hP hSne a d hcrit.1 had).criticalDistance_even
  have hacEven : Even ((cosetGraph S).dist a c) := by
    rcases hbEven with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  have hc : InMVertexOrbit S c :=
    mVertexOrbit_of_even_dist S hcrit.1 hacEven
  have hupper : (cosetGraph S).dist u c ≤ criticalDistance S :=
    neighbor_dist_le_frame_endpoint S had hdu hleft
  have hdist : (cosetGraph S).dist u c = criticalDistance S := by
    apply le_antisymm hupper
    by_contra hnot
    have hlt : (cosetGraph S).dist u c < criticalDistance S := by omega
    have htri := (cosetGraph_connected S).dist_triangle
      (u := u) (v := c) (w := a')
    have hua'Even : Even ((cosetGraph S).dist u a') :=
      even_dist_of_mVertexOrbits S hu
        (criticalPair_path T hTS hP hSne a a' hcrit hb).opposite_inMVertexOrbit
    have hua' : (cosetGraph S).dist u a' ≤ criticalDistance S := by
      rcases hua'Even with ⟨k, hk⟩
      rcases hbEven with ⟨l, hl⟩
      omega
    have hZuA' : vertexZ S u ≤ stabilizer S a' :=
      vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne hu hb hua'
    exact hescape (le_inf hZuC hZuA')
  refine ⟨hu, hdist, ?_⟩
  intro hkernel
  have hkernelA' : neighborhoodKernel S c ≤ stabilizer S a' :=
    neighborhoodKernel_le_stabilizer_of_dist_two S T hTS hc hright
  exact hescape (le_inf (fun z hz => (hkernel hz).1)
    (hkernel.trans hkernelA'))

private theorem subgroup_le_mapped_center_of_omega_generation
    {H : Type*} [Group H] (C E Q Z G : Subgroup H)
    (hCE : C ≤ omegaOneCenterAmbient E)
    (hCQ : C ≤ Q)
    (hZQ : Z ≤ omegaOneCenterAmbient Q)
    (hEG : E ≤ G)
    (hgen : E ⊔ Z = G) :
    C ≤ (Subgroup.center G).map G.subtype := by
  have hCcentE : C ≤ Subgroup.centralizer E := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (mem_omegaOneCenterAmbient_iff E c).mp (hCE hc) |>.2.2 e he
  have hCcentZ : C ≤ Subgroup.centralizer Z := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff Q z).mp
      (hZQ hz) |>.2.2 c (hCQ hc)).symm
  have hGcentC : G ≤ Subgroup.centralizer C := by
    rw [← hgen]
    exact sup_le (Subgroup.le_centralizer_iff.mp hCcentE)
      (Subgroup.le_centralizer_iff.mp hCcentZ)
  intro c hc
  have hcG : c ∈ G :=
    hEG ((mem_omegaOneCenterAmbient_iff E c).mp (hCE hc) |>.1)
  refine ⟨⟨c, hcG⟩, ?_, rfl⟩
  apply (Subgroup.mem_center_iff).2
  intro g
  apply Subtype.ext
  exact (hGcentC g.property c hc).symm

private theorem finalCommutator_central [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c d u : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (had : Adjacent S a d) (hdu : Adjacent S d u)
    (hdistTwo : (cosetGraph S).dist a u = 2)
    (hc : InMVertexOrbit S c)
    (hshift : IsCriticalPair S u c)
    (hleft : (cosetGraph S).dist a c + 2 = criticalDistance S)
    (hright : (cosetGraph S).dist c a' = 2)
    (hgenerate : edgeTwoCore S a d ⊔ vertexZ S a' = stabilizer S a)
    (hZa'Omega : vertexZ S a' ≤
      omegaOneCenterAmbient (vertexTwoCore S a'))
    (htwo : 2 < criticalDistance S) :
    ⁅vertexZ S u, vertexZ S c⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
  let E := edgeTwoCore S a d
  let C := ⁅vertexZ S u, vertexZ S c⁆
  have hu : InMVertexOrbit S u := hshift.1
  have hau : a ≠ u := by
    intro hau
    subst u
    simp at hdistTwo
  have hEeq : edgeTwoCore S u a = E :=
    edgeTwoCore_distanceTwo S T hTS a d u hcrit.1 hu had hdu hau
  have hlocalAD := criticalDistance_basic S T hTS hP hSne a d hcrit.1 had
  have hEGu : E ≤ stabilizer S u := by
    intro x hx
    exact (hlocalAD.edgeCore_le_neighbor_kernel hx).2 u hdu
  have hEp : IsPGroup 2 E :=
    edgeTwoCore_isPGroup (stabilizer S a) (stabilizer S d)
  obtain ⟨hZcKa, hZcKa'⟩ :=
    finalStrictKernelInclusions S hc hleft hright htwo
  have hKaE : neighborhoodKernel S a ≤ E := by
    change neighborhoodKernel S a ≤ edgeTwoCore S a d
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d hcrit.1 had]
    intro x hx
    exact ⟨hx.1, hx.2 d had⟩
  have hZcE : vertexZ S c ≤ E := hZcKa.trans hKaE
  have hQuKu : vertexTwoCore S u ≤ neighborhoodKernel S u :=
    vertexTwoCore_le_neighborhoodKernel S T hTS hu (adjacent_symm S hdu)
  have hKuGa : neighborhoodKernel S u ≤ stabilizer S a :=
    neighborhoodKernel_le_stabilizer_of_dist_two S T hTS hu (by
      simpa [SimpleGraph.dist_comm] using hdistTwo)
  have hQuE : vertexTwoCore S u ≤ E := by
    change vertexTwoCore S u ≤ edgeTwoCore S a d
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d hcrit.1 had]
    intro x hx
    have hxK := hQuKu hx
    exact ⟨hKuGa hxK, hxK.2 d (adjacent_symm S hdu)⟩
  obtain ⟨_hWshift, _hcInGu, hshift22⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA u c hshift hb
  have hPE : vertexZ S c ⊔ vertexTwoCore S u ≤ E :=
    sup_le hZcE hQuE
  have hEP : E ≤ vertexZ S c ⊔ vertexTwoCore S u :=
    le_reverse_sourceSylow S c u E hEGu hEp hZcE hshift22.sourceSylow
  have hPEeq : vertexZ S c ⊔ vertexTwoCore S u = E :=
    le_antisymm hPE hEP
  have hsource := hshift22.sourceOmegaCenter
  rw [hPEeq] at hsource
  have hComega : C ≤ omegaOneCenterAmbient E := by
    rw [hsource]
    exact le_sup_left
  obtain ⟨mid, hcmid, hmida'⟩ := exists_common_neighbor_of_dist_two S hright
  have ha'Orbit :=
    (criticalPair_path T hTS hP hSne a a' hcrit hb).opposite_inMVertexOrbit
  have hKa'Q : neighborhoodKernel S a' = vertexTwoCore S a' :=
    neighborhoodKernel_eq_vertexTwoCore S T hTS ha'Orbit
      (adjacent_symm S hmida')
  have hshiftPath := criticalPair_path T hTS hP hSne u c hshift hb
  have hCQ : C ≤ vertexTwoCore S a' := by
    exact hshiftPath.commutator_le_intersection.trans inf_le_right |>.trans
      (hZcKa'.trans (le_of_eq hKa'Q))
  have hEGa : E ≤ stabilizer S a :=
    (edgeTwoCore_le_inf S a d).trans inf_le_left
  exact subgroup_le_mapped_center_of_omega_generation C E
    (vertexTwoCore S a') (vertexZ S a') (stabilizer S a)
    hComega hCQ hZa'Omega hEGa hgenerate

private theorem isInvariantBy_map_equiv
    {G : Type*} [Group G] (e : G ≃* G) (N K : Subgroup G)
    (h : IsInvariantBy N K) :
    IsInvariantBy (N.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  intro k hk n hn
  rw [Subgroup.mem_map_equiv] at hk hn ⊢
  simpa only [map_mul, map_inv] using h (e.symm k) hk (e.symm n) hn

private theorem isInvariantBy_of_subgroupOf_normal
    {G : Type*} [Group G] (N K : Subgroup G)
    (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) :
    IsInvariantBy N K := by
  intro k hk n hn
  have hn' : (⟨n, hNK hn⟩ : K) ∈ N.subgroupOf K := hn
  exact hN.conj_mem _ hn' ⟨k, hk⟩

private theorem no_common_invariant_at_translated_base_edge [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (z : FreeAmalgam S) (N : Subgroup (FreeAmalgam S))
    (hNMle : N ≤ stabilizer S (mVertex S z))
    (hNHle : N ≤ stabilizer S (hVertex S z))
    (hNM : IsInvariantBy N (stabilizer S (mVertex S z)))
    (hNH : IsInvariantBy N (stabilizer S (hVertex S z))) : N = ⊥ := by
  let c : FreeAmalgam S ≃* FreeAmalgam S := MulAut.conj z⁻¹
  let N₀ : Subgroup (FreeAmalgam S) := N.map c.symm.toMonoidHom
  have hmVertex : mVertex S z = act S z (mVertex S 1) := by simp
  have hhVertex : hVertex S z = act S z (hVertex S 1) := by simp
  have hMmap : stabilizer S (mVertex S z) =
      (stabilizer S (mVertex S 1)).map c.toMonoidHom := by
    rw [hmVertex, stabilizer_act]
  have hHmap : stabilizer S (hVertex S z) =
      (stabilizer S (hVertex S 1)).map c.toMonoidHom := by
    rw [hhVertex, stabilizer_act]
  have hMback : (stabilizer S (mVertex S z)).map c.symm.toMonoidHom =
      stabilizer S (mVertex S 1) :=
    (Subgroup.map_symm_eq_iff_map_eq (e := c)
      (H := stabilizer S (mVertex S z)) (stabilizer S (mVertex S 1))).2
        hMmap.symm
  have hHback : (stabilizer S (hVertex S z)).map c.symm.toMonoidHom =
      stabilizer S (hVertex S 1) :=
    (Subgroup.map_symm_eq_iff_map_eq (e := c)
      (H := stabilizer S (hVertex S z)) (stabilizer S (hVertex S 1))).2
        hHmap.symm
  have hN₀M : N₀ ≤ stabilizer S (mVertex S 1) := by
    rw [← hMback]
    exact Subgroup.map_mono hNMle
  have hN₀H : N₀ ≤ stabilizer S (hVertex S 1) := by
    rw [← hHback]
    exact Subgroup.map_mono hNHle
  have hN₀invM : IsInvariantBy N₀ (stabilizer S (mVertex S 1)) := by
    rw [← hMback]
    exact isInvariantBy_map_equiv c.symm N (stabilizer S (mVertex S z)) hNM
  have hN₀invH : IsInvariantBy N₀ (stabilizer S (hVertex S 1)) := by
    rw [← hHback]
    exact isInvariantBy_map_equiv c.symm N (stabilizer S (hVertex S z)) hNH
  have hN₀S : N₀ ≤ Sbar S := by
    rw [← base_edge_stabilizer]
    exact le_inf hN₀M hN₀H
  have hN₀bot : N₀ = ⊥ := no_nontrivial_common_invariant S T hTS hP N₀ hN₀S
    (by simpa [stabilizer_m_base] using hN₀invM)
    (by simpa [stabilizer_h_base] using hN₀invH)
  exact (Subgroup.map_eq_bot_iff_of_injective N c.symm.injective).mp hN₀bot

private theorem no_common_normal_at_adjacent [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (a b : Vertex S) (hab : Adjacent S a b)
    (N : Subgroup (FreeAmalgam S))
    (hNle : N ≤ stabilizer S a ⊓ stabilizer S b)
    (hNa : (N.subgroupOf (stabilizer S a)).Normal)
    (hNb : (N.subgroupOf (stabilizer S b)).Normal) : N = ⊥ := by
  obtain ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
    (adjacent_iff_exists_common S a b).1 hab
  · apply no_common_invariant_at_translated_base_edge S T hTS hP z N
      (hNle.trans inf_le_left) (hNle.trans inf_le_right)
    · exact isInvariantBy_of_subgroupOf_normal N _
        (hNle.trans inf_le_left) hNa
    · exact isInvariantBy_of_subgroupOf_normal N _
        (hNle.trans inf_le_right) hNb
  · apply no_common_invariant_at_translated_base_edge S T hTS hP z N
      (hNle.trans inf_le_right) (hNle.trans inf_le_left)
    · exact isInvariantBy_of_subgroupOf_normal N _
        (hNle.trans inf_le_right) hNb
    · exact isInvariantBy_of_subgroupOf_normal N _
        (hNle.trans inf_le_left) hNa


public theorem criticalPair_distanceTwoShift
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (aPrimeMinusTwo : Vertex S)
    (hframe : DistanceTwoShift.Frame S a a' aPrimeMinusTwo) :
    ∃ aMinusTwo : Vertex S,
      DistanceTwoShift.Conclusion S a a' aPrimeMinusTwo aMinusTwo := by
  classical
  obtain ⟨aMinusOne, haaMinusOne, hgenerate⟩ :=
    criticalPair_generatingPredecessor
      S T hTS hP hSne hA a a' hcrit hb
  obtain ⟨V, hZaV, hVp, hVE, hVnormalMiddle, hVframe,
      hNeighborsV, hVminimal⟩ :=
    neighborCenterClosure S T hTS hP hSne a aMinusOne aPrimeMinusTwo
      hcrit.1 haaMinusOne hb hframe.left_length
  obtain ⟨hW, ha', hinputs⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA a a' hcrit hb
  have hVnotRight : ¬ V ≤ stabilizer S a' := by
    intro hVright
    obtain ⟨_hW', _ha, hreverse⟩ :=
      criticalPair_sl2Two S T hTS hP hSne hA a' a
        hinputs.critical.reverse_critical hb
    have hVsource : V ≤ vertexZ S a ⊔ vertexTwoCore S a' :=
      le_reverse_sourceSylow S a a' V hVright hVp hZaV
        hreverse.sourceSylow
    have hcomm : ⁅V, vertexZ S a'⁆ ≤ V :=
      (neighborClosure_commutator_le S a a' V hVright hVsource hinputs).trans hZaV
    have hZnormalizes : vertexZ S a' ≤
        Subgroup.normalizer (V : Set (FreeAmalgam S)) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm
    have hVD : V ≤ stabilizer S aMinusOne :=
      hVE.trans ((edgeTwoCore_le_inf S a aMinusOne).trans inf_le_right)
    have hMiddleNormalizes : stabilizer S aMinusOne ≤
        Subgroup.normalizer (V : Set (FreeAmalgam S)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVD).mp hVnormalMiddle
    have hEnormalizes : edgeTwoCore S a aMinusOne ≤
        Subgroup.normalizer (V : Set (FreeAmalgam S)) :=
      ((edgeTwoCore_le_inf S a aMinusOne).trans inf_le_right).trans
        hMiddleNormalizes
    have hLeftNormalizes : stabilizer S a ≤
        Subgroup.normalizer (V : Set (FreeAmalgam S)) := by
      rw [← hgenerate]
      exact sup_le hEnormalizes hZnormalizes
    have hVleft : V ≤ stabilizer S a :=
      hVE.trans ((edgeTwoCore_le_inf S a aMinusOne).trans inf_le_left)
    have hVnormalLeft : (V.subgroupOf (stabilizer S a)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVleft).mpr hLeftNormalizes
    have hVbot : V = ⊥ :=
      no_common_normal_at_adjacent S T hTS hP a aMinusOne haaMinusOne V
        (le_inf hVleft hVD) hVnormalLeft hVnormalMiddle
    have hZane : vertexZ S a ≠ ⊥ := by
      intro hZa
      apply hcrit.2.2
      rw [hZa]
      exact bot_le
    apply hZane
    apply le_bot_iff.mp
    rw [← hVbot]
    exact hZaV
  have hNotAll : ¬ ∀ u : Vertex S,
      Adjacent S aMinusOne u → vertexZ S u ≤ stabilizer S a' := by
    intro hAll
    exact hVnotRight (hVminimal (stabilizer S a') hAll)
  push Not at hNotAll
  obtain ⟨aMinusTwo, haMinusOneaMinusTwo, hEscapeRight⟩ := hNotAll
  have haNe : a ≠ aMinusTwo := by
    intro hEq
    subst aMinusTwo
    exact hEscapeRight hinputs.left_Z_le_right_stabilizer
  have haMinusTwoOrbit : InMVertexOrbit S aMinusTwo :=
    neighbor_inMVertexOrbit_of_commonNeighbor S hcrit.1 haaMinusOne
      haMinusOneaMinusTwo
  have hdistTwo : (cosetGraph S).dist a aMinusTwo = 2 :=
    dist_two_of_commonNeighbor S hcrit.1 haMinusTwoOrbit haaMinusOne
      haMinusOneaMinusTwo haNe
  have hEscapeInf : ¬ vertexZ S aMinusTwo ≤
      stabilizer S aPrimeMinusTwo ⊓ stabilizer S a' := by
    intro hle
    exact hEscapeRight (hle.trans inf_le_right)
  have hshifted : IsCriticalPair S aMinusTwo aPrimeMinusTwo :=
    shiftedCritical_of_escape S T hTS hP hSne
      a a' aPrimeMinusTwo aMinusOne aMinusTwo hcrit hb
      haaMinusOne haMinusOneaMinusTwo hframe.left_length
      hframe.right_length
      ((hNeighborsV aMinusTwo haMinusOneaMinusTwo).trans hVframe)
      hEscapeInf
  have hPrimeMinusTwoOrbit : InMVertexOrbit S aPrimeMinusTwo :=
    (criticalPair_path T hTS hP hSne aMinusTwo aPrimeMinusTwo hshifted hb)
      |>.opposite_inMVertexOrbit
  refine ⟨aMinusTwo, {
    distance_two := hdistTwo
    escapes_endpoint_intersection := hEscapeInf
    shifted_critical := hshifted
    generates_left_stabilizer := ?_
    commutator_central_of_two_lt := ?_
  }⟩
  · rw [edgeTwoCore_distanceTwo S T hTS a aMinusOne aMinusTwo
      hcrit.1 haMinusTwoOrbit haaMinusOne haMinusOneaMinusTwo haNe]
    exact hgenerate
  · intro htwo
    exact finalCommutator_central S T hTS hP hSne hA
      a a' aPrimeMinusTwo aMinusOne aMinusTwo hcrit hb
      haaMinusOne haMinusOneaMinusTwo hdistTwo hPrimeMinusTwoOrbit
      hshifted hframe.left_length hframe.right_length hgenerate
      hinputs.right_Z_le_coreOmega htwo

end Stellmacher.PushingUp
