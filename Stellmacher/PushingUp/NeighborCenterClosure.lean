module

public import Stellmacher.PushingUp.IncidentEdgeCore
public import Stellmacher.PushingUp.CriticalPairPath

/-!
# The neighbor-center closure at a predecessor vertex

This module isolates the subgroup constructed in Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), proof of (2.3), journal p.12.  Along an edge
`a ~ d`, let `V` be the image in the free amalgam of the normal closure in
`G_d` of `Z_a`.  Under condition (P) and a frame
`dist(a,c) + 2 = b`, the theorem packages the facts used later: `V` is a
2-subgroup of the incident edge core, is normal in `G_d`, lies in `G_c`,
contains every center subgroup at a neighbor of `d`, and is the least ambient
subgroup with that containment property.

The proof uses (1.3) through the critical-distance local package to put
`Z_a` in the incident edge core, whose exact stabilizer identity is supplied
by `IncidentEdgeCore`.  Local transitivity and conjugation-equivariance of
vertex centers identify the normal-closure generators with precisely the
neighbor centers.  The frame distance bound and `CriticalPairPath` then put
each generator in `G_c`.  All action transport and closure-induction helpers
remain private; the sole public declaration is the existential conjunction
needed by (2.3).  No finiteness of the vertex set or free amalgam is assumed.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

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

private theorem neighbor_inMVertexOrbit_of_commonNeighbor [Finite M]
    (S : Subgroup M) {a d u : Vertex S}
    (ha : InMVertexOrbit S a) (had : Adjacent S a d)
    (hdu : Adjacent S d u) : InMVertexOrbit S u := by
  obtain ⟨g, hg, hgu⟩ := stabilizer_transitive_neighbors S d
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

private theorem omegaOneCenterAmbient_le
    {G : Type*} [Group G] (Q : Subgroup G) :
    omegaOneCenterAmbient Q ≤ Q := by
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff Q x).mp hx |>.1

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

private theorem normalClosure_vertexZ_map_le_of_neighbors [Finite M]
    (S : Subgroup M) (a d : Vertex S) (had : Adjacent S d a)
    (K : Subgroup (FreeAmalgam S))
    (hK : ∀ u : Vertex S, Adjacent S d u → vertexZ S u ≤ K) :
    (Subgroup.normalClosure
        ((vertexZ S a).subgroupOf (stabilizer S d) :
          Set (stabilizer S d))).map (stabilizer S d).subtype ≤ K := by
  intro x hx
  obtain ⟨xD, hxD, rfl⟩ := hx
  change xD ∈ Subgroup.closure
    (Group.conjugatesOfSet
      ((vertexZ S a).subgroupOf (stabilizer S d) :
        Set (stabilizer S d))) at hxD
  induction hxD using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨z, hz, hzx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, hg⟩ := isConj_iff.mp hzx
      rw [← hg]
      have hgd : act S (g : FreeAmalgam S) d = d := g.property
      have hginvd : act S (g : FreeAmalgam S)⁻¹ d = d := by
        have hmem := (stabilizer S d).inv_mem g.property
        exact hmem
      have hAdj : Adjacent S d (act S (g : FreeAmalgam S)⁻¹ a) := by
        have h := (adjacent_act_iff S (g : FreeAmalgam S)⁻¹ d a).2 had
        simpa [hginvd] using h
      apply hK (act S (g : FreeAmalgam S)⁻¹ a) hAdj
      rw [vertexZ_act]
      refine ⟨(z : FreeAmalgam S), hz, ?_⟩
      simp [mul_assoc]
  | one => exact K.one_mem
  | mul x y _ _ hx hy => exact K.mul_mem hx hy
  | inv x _ hx => exact K.inv_mem hx

public theorem neighborCenterClosure [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a d c : Vertex S)
    (ha : InMVertexOrbit S a) (had : Adjacent S a d)
    (hb : 0 < criticalDistance S)
    (hframe : (cosetGraph S).dist a c + 2 = criticalDistance S) :
    ∃ V : Subgroup (FreeAmalgam S),
      vertexZ S a ≤ V ∧
      IsPGroup 2 V ∧
      V ≤ edgeTwoCore S a d ∧
      (V.subgroupOf (stabilizer S d)).Normal ∧
      V ≤ stabilizer S c ∧
      (∀ u : Vertex S, Adjacent S d u → vertexZ S u ≤ V) ∧
      ∀ K : Subgroup (FreeAmalgam S),
        (∀ u : Vertex S, Adjacent S d u → vertexZ S u ≤ K) → V ≤ K := by
  classical
  let D := stabilizer S d
  let A : Subgroup D := (vertexZ S a).subgroupOf D
  let N : Subgroup D := Subgroup.normalClosure (A : Set D)
  let V : Subgroup (FreeAmalgam S) := N.map D.subtype
  let E := edgeTwoCore S a d
  have hlocal := criticalDistance_basic S T hTS hP hSne a d ha had
  have hZaQ : vertexZ S a ≤ vertexTwoCore S a := by
    exact hlocal.vertexZ_le_coreOmega_or_distance_zero
      |>.resolve_right (Nat.ne_of_gt hb)
      |>.trans (omegaOneCenterAmbient_le (vertexTwoCore S a))
  have hQkernel : vertexTwoCore S a ≤ neighborhoodKernel S a :=
    sylowSubgroupIn_le hlocal.twoCore_sylow_kernel
  have hQedge : vertexTwoCore S a ≤ E := by
    rw [show E = stabilizer S a ⊓ stabilizer S d from
      incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d ha had]
    intro x hx
    have hxK := hQkernel hx
    exact ⟨hxK.1, hxK.2 d had⟩
  have hZaE : vertexZ S a ≤ E := hZaQ.trans hQedge
  have hED : E ≤ D := hlocal.edgeCore_le_neighbor_stabilizer
  have hZaD : vertexZ S a ≤ D := hZaE.trans hED
  have hNle : N ≤ E.subgroupOf D := by
    let _ : (E.subgroupOf D).Normal := hlocal.edgeCore_normal_neighbor
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact hZaE hx
  have hVE : V ≤ E := by
    rintro x ⟨xD, hxD, rfl⟩
    exact hNle hxD
  have hZaV : vertexZ S a ≤ V := by
    intro x hx
    let xD : D := ⟨x, hZaD hx⟩
    refine ⟨xD, ?_, rfl⟩
    exact Subgroup.subset_normalClosure (show xD ∈ A from hx)
  have hVp : IsPGroup 2 V :=
    (edgeTwoCore_isPGroup (stabilizer S a) (stabilizer S d)).to_le hVE
  have hsub : V.subgroupOf D = N := by
    ext x
    constructor
    · intro hx
      change (x : FreeAmalgam S) ∈ V at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hxy : y = x := Subtype.ext hyx
      simpa [hxy] using hy
    · intro hx
      change (x : FreeAmalgam S) ∈ V
      exact ⟨x, hx, rfl⟩
  have hVnormalD : (V.subgroupOf D).Normal := by
    rw [hsub]
    infer_instance
  have hVframe : V ≤ stabilizer S c := by
    apply normalClosure_vertexZ_map_le_of_neighbors S a d
      (adjacent_symm S had)
    intro u hdu
    have hu : InMVertexOrbit S u :=
      neighbor_inMVertexOrbit_of_commonNeighbor S ha had hdu
    apply vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne hu hb
    exact neighbor_dist_le_frame_endpoint S had hdu hframe
  have hNeighborsV : ∀ u : Vertex S,
      Adjacent S d u → vertexZ S u ≤ V := by
    intro u hdu
    obtain ⟨g, hgd, hgu⟩ := stabilizer_transitive_neighbors S d
      (adjacent_symm S had) hdu
    intro z hz
    rw [← hgu, vertexZ_act] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    let xD : D := ⟨x, hZaD hx⟩
    let gD : D := ⟨g, hgd⟩
    have hxVD : xD ∈ V.subgroupOf D := hZaV hx
    have hconj := hVnormalD.conj_mem xD hxVD gD⁻¹
    change ((gD⁻¹ * xD * (gD⁻¹)⁻¹ : D) : FreeAmalgam S) ∈ V at hconj
    simpa [xD, gD, MulAut.conj_apply, mul_assoc] using hconj
  refine ⟨V, hZaV, hVp, hVE, hVnormalD, hVframe, hNeighborsV, ?_⟩
  intro K hK
  exact normalClosure_vertexZ_map_le_of_neighbors S a d
    (adjacent_symm S had) K hK

end Stellmacher.PushingUp

