module

public import Stellmacher.PushingUp.CriticalClosure
public import Stellmacher.PushingUp.BicentralClosureCommutator

/-!
# Containment of the critical closure after conjugation

This module proves step (2) of Stellmacher, *Pushing up*, Arch. Math. 46
(1986), (2.4). Assume a critical pair of distance at least six, the shifted
pair from (2.3), and the chosen conjugator in the shifted left stabilizer
whose two endpoint centers generate modulo its 2-core. The normal closure
of the shifted center in the original left stabilizer, joined with the
original vertex center, lies in the translated opposite stabilizer.

A shortest path supplies the source's offsets four and six. The closure
radius bound and distance-two core containment select a stabilizer containing
the closure whose core it escapes. If this vertex center lies in the original
core, the bicentral closure-commutator theorem contradicts the escape. Otherwise
reverse core escape gives a critical pair, and the literal source Sylow omega
center identity makes its commutator central on the common Sylow subgroup.
Short distances and the chosen generation make it central on the shifted
stabilizer. The conjugator therefore fixes it; translating back places it
inside the untransformed offset center. That center is within four steps of
the original right endpoint, so the original generation equation makes the
commutator central on the left, contradicting the natural-module clause.

All path and commutator calculations are private. No finiteness of the vertex
set or free amalgam is assumed; only finite vertex stabilizers are used.
-/

namespace Stellmacher.PushingUp
open scoped commutatorElement
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem bound_exists_common_neighbor_of_dist_two [Finite M]
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

private theorem bound_sylowSubgroupIn_le
    {G : Type*} [Group G] {P K : Subgroup G}
    (h : IsSylowSubgroupIn P K) : P ≤ K := by
  obtain ⟨T, hT⟩ := h
  rw [← hT]
  exact Subgroup.map_subtype_le _

private theorem bound_edgeTwoCore_isPGroup
    {G : Type*} [Group G] (A B : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient (A ⊓ B)) := by
  unfold twoCoreAmbient
  exact (pCore_isPGroup (p := 2) (G := ↥(A ⊓ B))).map
    (A ⊓ B : Subgroup G).subtype

private theorem bound_omegaOneCenterAmbient_le
    {G : Type*} [Group G] (Q : Subgroup G) :
    omegaOneCenterAmbient Q ≤ Q := by
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff Q x).mp hx |>.1

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
    exact (vertexZ_le_neighborhoodKernel_of_dist_lt S hx hlt hz).1
  · have heq : (cosetGraph S).dist x y = criticalDistance S := by omega
    by_cases hker : vertexZ S x ≤ neighborhoodKernel S y
    · intro z hz
      exact (hker hz).1
    · exact (criticalPair_path T hTS hP hSne x y ⟨hx, heq, hker⟩ hb)
        |>.left_Z_le_right_stabilizer

private theorem bound_core_le_stabilizer_of_dist_two [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    {x y : Vertex S} (hx : InMVertexOrbit S x)
    (hxy : (cosetGraph S).dist x y = 2) :
    vertexTwoCore S x ≤ stabilizer S y := by
  obtain ⟨d, hxd, hdy⟩ := bound_exists_common_neighbor_of_dist_two S hxy
  have hlocal := localKernel_at_mEdge S T hTS x d hx hxd
  have hQK : vertexTwoCore S x ≤ neighborhoodKernel S x :=
    bound_sylowSubgroupIn_le hlocal.1
  have hQE : vertexTwoCore S x ≤ edgeTwoCore S x d := by
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS x d hx hxd]
    intro g hg
    exact ⟨(hQK hg).1, (hQK hg).2 d hxd⟩
  intro g hg
  exact (hlocal.2.2.2 (hQE hg)).2 y hdy

private theorem bound_escape_at_four_or_six [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (c yFour ySix : Vertex S) (V : Subgroup (FreeAmalgam S))
    (hFour : InMVertexOrbit S yFour) (hSix : InMVertexOrbit S ySix)
    (hFourC : (cosetGraph S).dist yFour c = 2)
    (hSixFour : (cosetGraph S).dist ySix yFour = 2)
    (hVSix : V ≤ stabilizer S ySix)
    (hVescape : ¬ V ≤ stabilizer S c) :
    (V ≤ stabilizer S yFour ∧ ¬ V ≤ vertexTwoCore S yFour) ∨
      (V ≤ stabilizer S ySix ∧ ¬ V ≤ vertexTwoCore S ySix) := by
  by_cases hVFour : V ≤ stabilizer S yFour
  · exact Or.inl ⟨hVFour, fun hVQ => hVescape (hVQ.trans
      (bound_core_le_stabilizer_of_dist_two S T hTS hFour hFourC))⟩
  · exact Or.inr ⟨hVSix, fun hVQ => hVFour (hVQ.trans
      (bound_core_le_stabilizer_of_dist_two S T hTS hSix hSixFour))⟩


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

private theorem mVertexOrbit_of_even_dist (S : Subgroup M)
    {x y : Vertex S} (hx : InMVertexOrbit S x)
    (heven : Even ((cosetGraph S).dist x y)) : InMVertexOrbit S y := by
  apply (inMVertexOrbit_iff_color_eq_false S y).2
  have hcolor := (even_dist_iff_color_eq S x y).1 heven
  rw [(inMVertexOrbit_iff_color_eq_false S x).1 hx] at hcolor
  exact hcolor.symm

private theorem bound_geodesic_offsets [Finite M]
    (S : Subgroup M) (c u : Vertex S)
    (hc : InMVertexOrbit S c)
    (hcu : (cosetGraph S).dist c u = criticalDistance S)
    (hb : 6 ≤ criticalDistance S) :
    ∃ yFour ySix : Vertex S,
      InMVertexOrbit S yFour ∧ InMVertexOrbit S ySix ∧
      (cosetGraph S).dist yFour c = 2 ∧
      (cosetGraph S).dist ySix yFour = 2 ∧
      (cosetGraph S).dist ySix u + 4 = criticalDistance S := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist c u
  have hlen : p.length = criticalDistance S := hp.trans hcu
  let yFour := p.getVert 2
  let ySix := p.getVert 4
  have hfour : (cosetGraph S).dist c yFour = 2 := by
    have htake := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take 2)
    simpa [SimpleGraph.Walk.take_length, hlen, Nat.min_eq_left (by omega : 2 ≤ criticalDistance S)] using htake.symm
  have hsix : (cosetGraph S).dist c ySix = 4 := by
    have htake := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take 4)
    simpa [SimpleGraph.Walk.take_length, hlen, Nat.min_eq_left (by omega : 4 ≤ criticalDistance S)] using htake.symm
  have hbetween : (cosetGraph S).dist yFour ySix = 2 := by
    have hsub := ((p.drop 2).isSubwalk_take 2).trans (p.isSubwalk_drop 2)
    have htake := SimpleGraph.length_eq_dist_of_subwalk hp hsub
    have hlen' : ((p.drop 2).take 2).length = 2 := by
      simp only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, hlen]
      omega
    rw [hlen'] at htake
    simpa [yFour, ySix, SimpleGraph.Walk.drop_getVert] using htake.symm
  have htail : (cosetGraph S).dist ySix u + 4 = criticalDistance S := by
    have hdrop := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_drop 4)
    simp only [SimpleGraph.Walk.drop_length, hlen] at hdrop
    change criticalDistance S - 4 = (cosetGraph S).dist ySix u at hdrop
    omega
  refine ⟨yFour, ySix, ?_, ?_, ?_, ?_, htail⟩
  · exact mVertexOrbit_of_even_dist S hc (by rw [hfour]; decide)
  · exact mVertexOrbit_of_even_dist S hc (by rw [hsix]; decide)
  · simpa [SimpleGraph.dist_comm] using hfour
  · simpa [SimpleGraph.dist_comm] using hbetween


private theorem adjacent_of_mOrbit (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) :
    ∃ b : Vertex S, Adjacent S a b := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g (hVertex S 1), ?_⟩
  exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2
    (base_adjacent S)

private theorem vertexZ_le_coreOmega_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) := by
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  exact
    (criticalDistance_basic S T hTS hP hSne a b ha hab).vertexZ_le_coreOmega_or_distance_zero
      |>.resolve_right (Nat.ne_of_gt hb)

private theorem vertexZ_isPGroup_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    IsPGroup 2 (vertexZ S a) := by
  have hOmega : IsPGroup 2 (omegaOneCenterAmbient (vertexTwoCore S a)) := by
    let _ : IsElementaryAbelian 2
        (omegaOneCenterAmbient (vertexTwoCore S a)) :=
      omegaOneCenterAmbient_elementaryAbelian _
    exact IsElementaryAbelian.isPGroup 2 _
  exact hOmega.to_le
    (vertexZ_le_coreOmega_of_pos S T hTS hP hSne a ha hb)

private theorem bound_vertexZ_le_core_of_dist_lt [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    {x y : Vertex S} (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hxy : (cosetGraph S).dist x y < criticalDistance S) :
    vertexZ S x ≤ vertexTwoCore S y := by
  obtain ⟨d, hyd⟩ := adjacent_of_mOrbit S y hy
  rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS y d hy hyd]
  exact vertexZ_le_neighborhoodKernel_of_dist_lt S hx hxy

private theorem bound_core_of_commutator_central [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a : Vertex S) (ha : InMVertexOrbit S a) (hb : 0 < criticalDistance S)
    (U : Subgroup (FreeAmalgam S)) (hUG : U ≤ stabilizer S a)
    (hUp : IsPGroup 2 U)
    (hcomm : ⁅vertexZ S a, U⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype) :
    U ≤ vertexTwoCore S a := by
  by_contra hnot
  obtain ⟨a', hcrit⟩ := criticalPair_exists S T hTS hP hSne a ha
  exact criticalPair_commutator_not_le_center S T hTS hP hSne hA
    a a' hcrit hb U hUG hUp hnot hcomm


private theorem bound_inM_act (S : Subgroup M) (g : FreeAmalgam S)
    {v : Vertex S} (hv : InMVertexOrbit S v) : InMVertexOrbit S (act S g v) := by
  obtain ⟨z, rfl⟩ := hv
  exact ⟨z * g, by rw [act_mul]⟩

private theorem bound_choose_escape [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a u c : Vertex S)
    (ha : InMVertexOrbit S a) (hu : InMVertexOrbit S u)
    (hc : InMVertexOrbit S c)
    (hau : (cosetGraph S).dist a u = 2)
    (hcu : (cosetGraph S).dist c u = criticalDistance S)
    (hb : 6 ≤ criticalDistance S) (t : FreeAmalgam S)
    (htu : t ∈ stabilizer S u)
    (hescape : ¬ criticalClosure S a u ≤ stabilizer S (act S t c)) :
    ∃ y0 : Vertex S, InMVertexOrbit S y0 ∧
      ((cosetGraph S).dist y0 c = 2 ∨
        ((cosetGraph S).dist y0 c = 4 ∧
          vertexZ S (act S t y0) ≤ vertexTwoCore S a)) ∧
      criticalClosure S a u ≤ stabilizer S (act S t y0) ∧
      ¬ criticalClosure S a u ≤ vertexTwoCore S (act S t y0) ∧
      vertexZ S (act S t y0) ≤ stabilizer S a ∧
      vertexZ S (act S t y0) ≤ vertexTwoCore S u ∧
      (cosetGraph S).dist a (act S t y0) ≤ criticalDistance S := by
  obtain ⟨yFour, ySix, hFour, hSix, hFourC, hSixFour, hSixU⟩ :=
    bound_geodesic_offsets S c u hc hcu hb
  have htu' : act S t u = u := htu
  have hSixU' : (cosetGraph S).dist (act S t ySix) u + 4 =
      criticalDistance S := by
    have hd := cosetGraph_dist_act S t ySix u
    rw [htu'] at hd
    omega
  have hFourU : (cosetGraph S).dist yFour u + 2 ≤ criticalDistance S := by
    have htri := (cosetGraph_connected S).dist_triangle
      (u := yFour) (v := ySix) (w := u)
    have hFS : (cosetGraph S).dist yFour ySix = 2 := by
      simpa [SimpleGraph.dist_comm] using hSixFour
    omega
  have hFourU' : (cosetGraph S).dist (act S t yFour) u + 2 ≤
      criticalDistance S := by
    have hd := cosetGraph_dist_act S t yFour u
    rw [htu'] at hd
    omega
  have hFourA : (cosetGraph S).dist (act S t yFour) a ≤ criticalDistance S := by
    have htri := (cosetGraph_connected S).dist_triangle
      (u := act S t yFour) (v := u) (w := a)
    have hua : (cosetGraph S).dist u a = 2 := by
      simpa [SimpleGraph.dist_comm] using hau
    omega
  have hSixA : (cosetGraph S).dist (act S t ySix) a + 2 ≤ criticalDistance S := by
    have htri := (cosetGraph_connected S).dist_triangle
      (u := act S t ySix) (v := u) (w := a)
    have hua : (cosetGraph S).dist u a = 2 := by
      simpa [SimpleGraph.dist_comm] using hau
    omega
  have hVSix : criticalClosure S a u ≤ stabilizer S (act S t ySix) :=
    criticalClosure_le_stabilizer S T hTS hP hSne a u (act S t ySix)
      ha hu (by omega) hau (by simpa [SimpleGraph.dist_comm] using hSixA)
  have hFourAct := bound_inM_act S t hFour
  have hSixAct := bound_inM_act S t hSix
  have hFourC' : (cosetGraph S).dist (act S t yFour) (act S t c) = 2 := by
    rw [cosetGraph_dist_act, hFourC]
  have hSixFour' : (cosetGraph S).dist (act S t ySix) (act S t yFour) = 2 := by
    rw [cosetGraph_dist_act, hSixFour]
  rcases bound_escape_at_four_or_six S T hTS (act S t c)
      (act S t yFour) (act S t ySix) (criticalClosure S a u)
      hFourAct hSixAct hFourC' hSixFour' hVSix hescape with h4 | h6
  · refine ⟨yFour, hFour, Or.inl hFourC, h4.1, h4.2, ?_, ?_, ?_⟩
    · exact vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne hFourAct (by omega) hFourA
    · exact bound_vertexZ_le_core_of_dist_lt S T hTS hFourAct hu (by omega)
    · simpa [SimpleGraph.dist_comm] using hFourA
  · have hZSixQa : vertexZ S (act S t ySix) ≤ vertexTwoCore S a :=
      bound_vertexZ_le_core_of_dist_lt S T hTS hSixAct ha (by omega)
    refine ⟨ySix, hSix, Or.inr ⟨?_, hZSixQa⟩, h6.1, h6.2, ?_, ?_, ?_⟩
    · have htri := (cosetGraph_connected S).dist_triangle
        (u := c) (v := ySix) (w := u)
      have htri' := (cosetGraph_connected S).dist_triangle
        (u := ySix) (v := yFour) (w := c)
      have hcs : (cosetGraph S).dist c ySix = (cosetGraph S).dist ySix c :=
        SimpleGraph.dist_comm
      omega
    · exact vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne hSixAct (by omega) (by omega)
    · exact bound_vertexZ_le_core_of_dist_lt S T hTS hSixAct hu (by omega)
    · have hsa : (cosetGraph S).dist a (act S t ySix) = (cosetGraph S).dist (act S t ySix) a := SimpleGraph.dist_comm
      omega


private theorem bound_mapped_center_le_centralizer {H : Type*} [Group H]
    (G : Subgroup H) :
    (Subgroup.center G).map G.subtype ≤ Subgroup.centralizer (G : Set H) := by
  rintro r ⟨rG, hrG, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hrG) ⟨g, hg⟩)

private theorem bound_le_mapped_center {H : Type*} [Group H]
    (R G : Subgroup H) (hRG : R ≤ G)
    (hRC : R ≤ Subgroup.centralizer (G : Set H)) :
    R ≤ (Subgroup.center G).map G.subtype := by
  intro r hr
  refine ⟨⟨r, hRG hr⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hRC hr) g g.property

private theorem bound_central_of_generation {H : Type*} [Group H]
    (R E B G : Subgroup H) (hRG : R ≤ G)
    (hRE : R ≤ Subgroup.centralizer (E : Set H))
    (hRB : R ≤ Subgroup.centralizer (B : Set H)) (hgen : E ⊔ B = G) :
    R ≤ (Subgroup.center G).map G.subtype := by
  apply bound_le_mapped_center R G hRG
  apply Subgroup.le_centralizer_iff.mp
  rw [← hgen]
  exact sup_le (Subgroup.le_centralizer_iff.mp hRE)
    (Subgroup.le_centralizer_iff.mp hRB)

private theorem bound_core_centralizes_Z [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    vertexTwoCore S a ≤ Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) := by
  apply Subgroup.le_centralizer_iff.mp
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  exact (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) z).mp
    (vertexZ_le_coreOmega_of_pos S T hTS hP hSne a ha hb hz) |>.2.2

private theorem bound_Z_centralizes_Z_of_dist_lt [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a d : Vertex S)
    (ha : InMVertexOrbit S a) (hd : InMVertexOrbit S d)
    (hb : 0 < criticalDistance S)
    (hDist : (cosetGraph S).dist a d < criticalDistance S) :
    vertexZ S a ≤ Subgroup.centralizer (vertexZ S d : Set (FreeAmalgam S)) :=
  (bound_vertexZ_le_core_of_dist_lt S T hTS ha hd hDist).trans
    (bound_core_centralizes_Z S T hTS hP hSne d hd hb)

private theorem bound_commutator_le_Z [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (A : Subgroup (FreeAmalgam S)) (hAG : A ≤ stabilizer S a) :
    ⁅A, vertexZ S a⁆ ≤ vertexZ S a := by
  apply Subgroup.le_normalizer_iff_commutator_le_right.mp
  exact hAG.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (vertexZ_le_stabilizer S a)).mp (vertexZ_normal_stabilizer S a))

private theorem bound_critical_of_reverse_core_escape [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a y : Vertex S) (ha : InMVertexOrbit S a) (hy : InMVertexOrbit S y)
    (hb : 0 < criticalDistance S)
    (hZyGa : vertexZ S y ≤ stabilizer S a)
    (hZyNotQa : ¬ vertexZ S y ≤ vertexTwoCore S a)
    (hDist : (cosetGraph S).dist a y ≤ criticalDistance S) :
    IsCriticalPair S a y := by
  have hZaNotQy : ¬ vertexZ S a ≤ vertexTwoCore S y := by
    intro hZaQy
    have hzero : ⁅vertexZ S a, vertexZ S y⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hZaQy.trans (bound_core_centralizes_Z S T hTS hP hSne y hy hb))
    apply hZyNotQa
    apply bound_core_of_commutator_central S T hTS hP hSne hA a ha hb
      (vertexZ S y) hZyGa (vertexZ_isPGroup_of_pos S T hTS hP hSne y hy hb)
    rw [hzero]
    exact bot_le
  have hnotKernel : ¬ vertexZ S a ≤ neighborhoodKernel S y := by
    obtain ⟨d, hyd⟩ := adjacent_of_mOrbit S y hy
    rwa [mVertex_neighborhoodKernel_eq_twoCore S T hTS y d hy hyd]
  refine ⟨ha, ?_, hnotKernel⟩
  by_contra hne
  exact hnotKernel (vertexZ_le_neighborhoodKernel_of_dist_lt S ha (by omega))

private theorem bound_critical_commutator_central_sylow [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a y : Vertex S) (hcrit : IsCriticalPair S a y)
    (hb : 0 < criticalDistance S)
    (E : Subgroup (FreeAmalgam S)) (hEp : IsPGroup 2 E)
    (hEGa : E ≤ stabilizer S a)
    (hZyE : vertexZ S y ≤ E) (hQaE : vertexTwoCore S a ≤ E) :
    ⁅vertexZ S a, vertexZ S y⁆ ≤ (Subgroup.center E).map E.subtype := by
  obtain ⟨hW, hy, hsl⟩ := criticalPair_sl2Two S T hTS hP hSne hA a y hcrit hb
  have hEeq : vertexZ S y ⊔ vertexTwoCore S a = E :=
    le_antisymm (sup_le hZyE hQaE)
      (le_reverse_sourceSylow S y a E hEGa hEp hZyE hsl.sourceSylow)
  have hOmega : ⁅vertexZ S a, vertexZ S y⁆ ≤ omegaOneCenterAmbient E := by
    rw [← hEeq, hsl.sourceOmegaCenter]
    exact le_sup_left
  apply bound_le_mapped_center _ E
    (hOmega.trans (bound_omegaOneCenterAmbient_le E))
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  exact (mem_omegaOneCenterAmbient_iff E r).mp (hOmega hr) |>.2.2


private theorem bound_le_untranslated_Z_of_central [Finite M]
    (S : Subgroup M) (u y0 : Vertex S) (t : FreeAmalgam S)
    (ht : t ∈ stabilizer S u) (R : Subgroup (FreeAmalgam S))
    (hRc : R ≤ (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype)
    (hRZ : R ≤ vertexZ S (act S t y0)) : R ≤ vertexZ S y0 := by
  intro r hr
  have hrt : t * r = r * t :=
    Subgroup.mem_centralizer_iff.mp
      (bound_mapped_center_le_centralizer (stabilizer S u) (hRc hr)) t ht
  have hfix : (MulAut.conj t⁻¹) r = r := by
    change t⁻¹ * r * (t⁻¹)⁻¹ = r
    simp only [inv_inv]
    calc
      _ = t⁻¹ * (r * t) := mul_assoc _ _ _
      _ = t⁻¹ * (t * r) := by rw [← hrt]
      _ = r := by simp
  have hz := hRZ hr
  rw [vertexZ_act_eq_map] at hz
  obtain ⟨z, hz, hzr⟩ := hz
  have heq : z = r := (MulAut.conj t⁻¹).injective (hzr.trans hfix.symm)
  rwa [← heq]

private theorem bound_shift_centrality_tail [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a a' c u y0 : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 6 ≤ criticalDistance S) (hf : DistanceTwoShift.Frame S a a' c)
    (hs : DistanceTwoShift.Conclusion S a a' c u)
    (hy0 : InMVertexOrbit S y0) (hy0c : (cosetGraph S).dist y0 c = 2)
    (t : FreeAmalgam S) (ht : t ∈ stabilizer S u)
    (R : Subgroup (FreeAmalgam S)) (hRGa : R ≤ stabilizer S a)
    (hRc : R ≤ (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype)
    (hRZ : R ≤ vertexZ S (act S t y0)) :
    R ≤ (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
  have hRZ0 : R ≤ vertexZ S y0 :=
    bound_le_untranslated_Z_of_central S u y0 t ht R hRc hRZ
  have ha' : InMVertexOrbit S a' :=
    (criticalPair_path T hTS hP hSne a a' hcrit (by omega)).opposite_inMVertexOrbit
  have ha'y0 : (cosetGraph S).dist a' y0 < criticalDistance S := by
    have htri := (cosetGraph_connected S).dist_triangle (u := a') (v := c) (w := y0)
    have ha'c : (cosetGraph S).dist a' c = 2 := by
      simpa [SimpleGraph.dist_comm] using hf.right_length
    have hcy0 : (cosetGraph S).dist c y0 = 2 := by
      simpa [SimpleGraph.dist_comm] using hy0c
    omega
  have hZa'centR : vertexZ S a' ≤ Subgroup.centralizer (R : Set (FreeAmalgam S)) := by
    have hcent := bound_Z_centralizes_Z_of_dist_lt S T hTS hP hSne
      a' y0 ha' hy0 (by omega) ha'y0
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_iff.mp (hcent hz) r (hRZ0 hr)
  let E := edgeTwoCore S u a
  have hEGu : E ≤ stabilizer S u :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hRcentE : R ≤ Subgroup.centralizer (E : Set (FreeAmalgam S)) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_iff.mp
      (bound_mapped_center_le_centralizer (stabilizer S u) (hRc hr)) e (hEGu he)
  exact bound_central_of_generation R E (vertexZ S a') (stabilizer S a)
    hRGa hRcentE (Subgroup.le_centralizer_iff.mp hZa'centR)
    hs.generates_left_stabilizer


public theorem criticalClosure_le_translated_stabilizer [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 6 ≤ criticalDistance S) (hf : DistanceTwoShift.Frame S a a' c)
    (hs : DistanceTwoShift.Conclusion S a a' c u)
    (t : FreeAmalgam S) (ht : t ∈ stabilizer S u)
    (hgen : vertexZ S c ⊔ (vertexZ S c).map (MulAut.conj t⁻¹).toMonoidHom ⊔
      vertexTwoCore S u = stabilizer S u) :
    criticalClosure S a u ≤ stabilizer S (act S t c) := by
  by_contra hescape
  have hu := hs.shifted_critical.1
  have hc := (criticalPair_path T hTS hP hSne u c hs.shifted_critical
    (by omega)).opposite_inMVertexOrbit
  have hVQa : criticalClosure S a u ≤ vertexTwoCore S a :=
    criticalClosure_le_core S T hTS hP hSne a u hcrit.1 hu hs.distance_two (by omega)
  have hVtwo : IsPGroup 2 (criticalClosure S a u) :=
    ((pCore_isPGroup (p := 2) (G := stabilizer S a)).map
      (stabilizer S a).subtype).to_le hVQa
  let E := edgeTwoCore S u a
  obtain ⟨hQaP, hEP⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    a a' c u hcrit (by omega) hf hs
  have hQaE : vertexTwoCore S a ≤ E := by simpa only [E, hEP] using hQaP
  have hQuE : vertexTwoCore S u ≤ E := by
    change vertexTwoCore S u ≤ edgeTwoCore S u a
    rw [hEP]
    exact le_sup_right
  have hEinf : E ≤ stabilizer S u ⊓ stabilizer S a := Subgroup.map_subtype_le _
  have hEGu := hEinf.trans inf_le_left
  have hEGa := hEinf.trans inf_le_right
  have hEp : IsPGroup 2 E := bound_edgeTwoCore_isPGroup (stabilizer S u) (stabilizer S a)
  have hQaGu : vertexTwoCore S a ≤ stabilizer S u := hQaE.trans hEGu
  have hZuGa : vertexZ S u ≤ stabilizer S a :=
    vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne hu (by omega) (by
      have hdist := hs.distance_two
      rw [SimpleGraph.dist_comm]
      omega)
  have hgenE : E ⊔ vertexZ S (act S t c) = stabilizer S u := by
    change edgeTwoCore S u a ⊔ vertexZ S (act S t c) = stabilizer S u
    rw [hEP, vertexZ_act_eq_map]
    simpa [sup_assoc, sup_comm, sup_left_comm] using hgen
  obtain ⟨y0, hy0, hcases, hVGy, hVnotQy, hZyGa, hZyQu, hay⟩ :=
    bound_choose_escape S T hTS hP hSne a u c hcrit.1 hu hc hs.distance_two
      (by simpa [SimpleGraph.dist_comm] using hs.shifted_critical.2.1)
      hb t ht hescape
  let y := act S t y0
  have hy : InMVertexOrbit S y := bound_inM_act S t hy0
  have hct : InMVertexOrbit S (act S t c) := bound_inM_act S t hc
  have hZyE : vertexZ S y ≤ E := hZyQu.trans hQuE
  have hDist : (cosetGraph S).dist (act S t c) y < criticalDistance S := by
    change (cosetGraph S).dist (act S t c) (act S t y0) < criticalDistance S
    rw [cosetGraph_dist_act, SimpleGraph.dist_comm]
    rcases hcases with h4 | ⟨h6, _⟩ <;> omega
  have hZctCentZy : vertexZ S (act S t c) ≤
      Subgroup.centralizer (vertexZ S y : Set (FreeAmalgam S)) :=
    bound_Z_centralizes_Z_of_dist_lt S T hTS hP hSne
      (act S t c) y hct hy (by omega) hDist
  have hcentralGu (R : Subgroup (FreeAmalgam S))
      (hRZy : R ≤ vertexZ S y)
      (hRcentE : R ≤ Subgroup.centralizer (E : Set (FreeAmalgam S))) :
      R ≤ (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype := by
    apply bound_central_of_generation R E (vertexZ S (act S t c)) (stabilizer S u)
      (hRZy.trans (hZyE.trans hEGu)) hRcentE ?_ hgenE
    apply Subgroup.le_centralizer_iff.mp
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_iff.mp (hZctCentZy hz) r (hRZy hr)
  by_cases hZyQa : vertexZ S y ≤ vertexTwoCore S a
  · let R := ⁅criticalClosure S a u, vertexZ S y⁆
    have hRcA : R ≤ (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
      have hcore := criticalClosure_core_commutator_central S T hTS hP hSne hA a a' c u
        hcrit hb hf hs
      rw [Subgroup.commutator_comm] at hcore
      exact (Subgroup.commutator_mono le_rfl hZyQa).trans hcore
    have hRZy : R ≤ vertexZ S y := bound_commutator_le_Z S y (criticalClosure S a u) hVGy
    have hRcU := hcentralGu R hRZy (by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_iff.mp
        (bound_mapped_center_le_centralizer (stabilizer S a) (hRcA hr)) e (hEGa he))
    have hzero : R = ⊥ := by
      have hh := criticalClosure_commutator_eq_bot_of_bicentral S T hTS hP hSne hA
        a a' u c hcrit hs.shifted_critical (by omega) hQaGu hZuGa
        (vertexZ S y) hZyQa (vertexZ_isPGroup_of_pos S T hTS hP hSne y hy (by omega))
        hRcA
        hRcU
      exact hh
    apply hVnotQy
    apply bound_core_of_commutator_central S T hTS hP hSne hA y hy (by omega)
      (criticalClosure S a u) hVGy hVtwo
    rw [Subgroup.commutator_comm]
    change R ≤ _
    rw [hzero]
    exact bot_le
  · have hy0c : (cosetGraph S).dist y0 c = 2 := by
      rcases hcases with h4 | ⟨_, h6⟩
      · exact h4
      · exact False.elim (hZyQa h6)
    have hcritAY := bound_critical_of_reverse_core_escape S T hTS hP hSne hA
      a y hcrit.1 hy (by omega) hZyGa hZyQa hay
    let R := ⁅vertexZ S a, vertexZ S y⁆
    have hRZy : R ≤ vertexZ S y := bound_commutator_le_Z S y (vertexZ S a)
      ((vertexZ_self_le_criticalClosure S a u).trans hVGy)
    have hRcE : R ≤ (Subgroup.center E).map E.subtype :=
      bound_critical_commutator_central_sylow S T hTS hP hSne hA
        a y hcritAY (by omega) E hEp hEGa hZyE hQaE
    have hRcU := hcentralGu R hRZy
      (hRcE.trans (bound_mapped_center_le_centralizer E))
    have hRcA := bound_shift_centrality_tail S T hTS hP hSne a a' c u y0 hcrit
      hb hf hs hy0 hy0c t ht R (hRZy.trans hZyGa) hRcU hRZy
    apply hZyQa
    exact bound_core_of_commutator_central S T hTS hP hSne hA a hcrit.1 (by omega)
      (vertexZ S y) hZyGa (vertexZ_isPGroup_of_pos S T hTS hP hSne y hy (by omega)) hRcA


end Stellmacher.PushingUp
