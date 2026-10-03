module

public import Stellmacher.PushingUp.DistanceTwoShift
public import Stellmacher.ResidualCommutatorGeneratedModulo

/-!
# The distance-two residual commutator lies in the local module

For a critical pair of distance two, this module proves the first containment
in Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.2)(a), journal p.14:
the commutator of the vertex 2-core with the local 2-residual lies in the
canonical local module.

Apply the distance-two shift with the penultimate vertex equal to the left
endpoint.  Reverse applications of (2.2)(a), together with the distance-two
edge-core containment, the shared reverse-Sylow adapter from
`DistanceTwoShift`, and the omega-center clauses, show that the vertex
2-core commutes modulo its local module with each of the two shifted
generators.  The shift generation equality then makes the quotient by that
module a 2-group.  Consequently the local 2-residual is contained in those
generators modulo the module, which proves the required commutator
containment.

This is the exact local input needed by the distance-two structure case.  It
does not assume that the vertex set or free amalgam is finite.
-/

open scoped Pointwise
open BenderSuzuki External

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

private theorem commutator_le_normal_of_quotient_central
    {G : Type u} [Group G]
    (Q R C F Z : Subgroup G) (hZnormal : Z.Normal)
    (hQCZ : Q ≤ C ⊔ Z) (hR : R ≤ F ⊔ Z)
    (hCF : C ≤ Subgroup.centralizer (F : Set G)) :
    ⁅Q, R⁆ ≤ Z := by
  let _ : Z.Normal := hZnormal
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hZmap : Z.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := Z)).2
    simp [q, QuotientGroup.ker_mk']
  have hQmap : Q.map q ≤ C.map q := by
    have := Subgroup.map_mono (f := q) hQCZ
    rw [Subgroup.map_sup, hZmap, sup_bot_eq] at this
    exact this
  have hRmap : R.map q ≤ F.map q := by
    have := Subgroup.map_mono (f := q) hR
    rw [Subgroup.map_sup, hZmap, sup_bot_eq] at this
    exact this
  have hCFbot : ⁅C, F⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCF
  have hmappedBot : (⁅Q, R⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator]
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hQmap hRmap).trans
      (le_of_eq (by rw [← Subgroup.map_commutator, hCFbot, Subgroup.map_bot]))
  have hker := (Subgroup.map_eq_bot_iff (f := q) (H := ⁅Q, R⁆)).mp hmappedBot
  simpa [q, QuotientGroup.ker_mk'] using hker

private theorem sylowSubgroupIn_le
    {G : Type*} [Group G] {P K : Subgroup G}
    (h : IsSylowSubgroupIn P K) : P ≤ K := by
  obtain ⟨T, hT⟩ := h
  rw [← hT]
  exact Subgroup.map_subtype_le _

private theorem vertexTwoCore_isPGroup
    {M : Type u} [Group M] (S : Subgroup M) (a : AmalgamGraph.Vertex S) :
    IsPGroup 2 (vertexTwoCore S a) := by
  unfold vertexTwoCore twoCoreAmbient
  exact (pCore_isPGroup (p := 2) (G := AmalgamGraph.stabilizer S a)).map
    (AmalgamGraph.stabilizer S a).subtype

private theorem edgeTwoCore_isPGroup
    {M : Type u} [Group M] (S : Subgroup M)
    (a b : AmalgamGraph.Vertex S) : IsPGroup 2 (edgeTwoCore S a b) := by
  unfold edgeTwoCore twoCoreAmbient
  exact (pCore_isPGroup (p := 2)
    (G := ↑(AmalgamGraph.stabilizer S a ⊓ AmalgamGraph.stabilizer S b))).map
      (AmalgamGraph.stabilizer S a ⊓ AmalgamGraph.stabilizer S b).subtype

private theorem omegaOneCenterAmbient_le
    {G : Type*} [Group G] (Q : Subgroup G) :
    omegaOneCenterAmbient Q ≤ Q := by
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff Q x).mp hx |>.1

private theorem exists_commonNeighbor_of_dist_two
    {M : Type u} [Group M] (S : Subgroup M)
    (a u : AmalgamGraph.Vertex S)
    (hdist : (AmalgamGraph.cosetGraph S).dist a u = 2) :
    ∃ d : AmalgamGraph.Vertex S,
      AmalgamGraph.Adjacent S a d ∧ AmalgamGraph.Adjacent S d u := by
  obtain ⟨p, hp⟩ :=
    (AmalgamGraph.cosetGraph_connected S).exists_walk_length_eq_dist a u
  let d := p.getVert 1
  have hlen : p.length = 2 := hp.trans hdist
  have had : (AmalgamGraph.cosetGraph S).Adj a d := by
    simpa [d] using p.adj_getVert_succ (i := 0) (by omega)
  have hdu : (AmalgamGraph.cosetGraph S).Adj d u := by
    have h := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
    have hp2 : p.getVert 2 = u := p.getVert_of_length_le (by omega)
    simpa [d, hp2] using h
  exact ⟨d, (AmalgamGraph.cosetGraph_adj S a d).mp had,
    (AmalgamGraph.cosetGraph_adj S d u).mp hdu⟩

private theorem vertexTwoCore_le_endpointEdgeCore_of_dist_two
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a u : AmalgamGraph.Vertex S)
    (ha : InMVertexOrbit S a) (hu : InMVertexOrbit S u)
    (hdist : (AmalgamGraph.cosetGraph S).dist a u = 2) :
    vertexTwoCore S a ≤ edgeTwoCore S u a := by
  obtain ⟨d, had, hdu⟩ := exists_commonNeighbor_of_dist_two S a u hdist
  have hau : a ≠ u := by
    intro hau
    subst u
    simp at hdist
  have hQaKernel : vertexTwoCore S a ≤ AmalgamGraph.neighborhoodKernel S a :=
    sylowSubgroupIn_le (localKernel_at_mEdge S T hTS a d ha had).1
  have hQaEdge : vertexTwoCore S a ≤ edgeTwoCore S a d := by
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d ha had]
    intro q hq
    exact ⟨(hQaKernel hq).1, (hQaKernel hq).2 d had⟩
  rw [edgeTwoCore_distanceTwo S T hTS a d u ha hu had hdu hau]
  exact hQaEdge

private theorem edgeTwoCore_le_rightStabilizer
    {M : Type u} [Group M] (S : Subgroup M)
    (u a : AmalgamGraph.Vertex S) :
    edgeTwoCore S u a ≤ AmalgamGraph.stabilizer S a := by
  unfold edgeTwoCore twoCoreAmbient
  exact (Subgroup.map_subtype_le _).trans inf_le_right

private theorem edgeTwoCore_le_leftStabilizer
    {M : Type u} [Group M] (S : Subgroup M)
    (a u : Vertex S) :
    edgeTwoCore S a u ≤ stabilizer S a := by
  unfold edgeTwoCore twoCoreAmbient
  exact (Subgroup.map_subtype_le _).trans inf_le_left

private theorem edgeTwoCore_comm
    {M : Type u} [Group M] (S : Subgroup M)
    (a u : Vertex S) : edgeTwoCore S a u = edgeTwoCore S u a := by
  unfold edgeTwoCore
  rw [inf_comm]

private theorem commutator_le_of_source_sylow
    {G : Type u} [Group G]
    (Q A R Z : Subgroup G) (hZnormal : Z.Normal)
    (hQRZ : Q ≤ R ⊔ Z)
    (hRA : R ≤ Subgroup.centralizer (A : Set G)) :
    ⁅Q, A⁆ ≤ Z := by
  exact commutator_le_normal_of_quotient_central
    Q A R A Z hZnormal hQRZ le_sup_left hRA

private theorem commutator_sup_le_of_each
    {G : Type u} [Group G]
    (Q A B Z : Subgroup G) (hZnormal : Z.Normal)
    (hQA : ⁅Q, A⁆ ≤ Z) (hQB : ⁅Q, B⁆ ≤ Z) :
    ⁅Q, A ⊔ B⁆ ≤ Z := by
  let _ : Z.Normal := hZnormal
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hZmap : Z.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := Z)).2
    simp [q, QuotientGroup.ker_mk']
  have hQAmap : ⁅Q.map q, A.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    exact le_bot_iff.mp ((Subgroup.map_mono hQA).trans (le_of_eq hZmap))
  have hQBmap : ⁅Q.map q, B.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    exact le_bot_iff.mp ((Subgroup.map_mono hQB).trans (le_of_eq hZmap))
  have hQcentA : Q.map q ≤ Subgroup.centralizer (A.map q : Set (G ⧸ Z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQAmap
  have hQcentB : Q.map q ≤ Subgroup.centralizer (B.map q : Set (G ⧸ Z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQBmap
  have hQcentSup : Q.map q ≤
      Subgroup.centralizer ((A.map q ⊔ B.map q : Subgroup (G ⧸ Z)) : Set _) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hAle : A.map q ≤ Subgroup.centralizer ({x} : Set (G ⧸ Z)) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp (hQcentA hx) a ha).symm
    have hBle : B.map q ≤ Subgroup.centralizer ({x} : Set (G ⧸ Z)) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp (hQcentB hx) b hb).symm
    have hycent : y ∈ Subgroup.centralizer ({x} : Set (G ⧸ Z)) :=
      (sup_le hAle hBle) hy
    exact (Subgroup.mem_centralizer_iff.mp hycent x (by simp)).symm
  have hmappedBot : (⁅Q, A ⊔ B⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_sup,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hQcentSup
  have hker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := ⁅Q, A ⊔ B⁆)).mp hmappedBot
  simpa [q, QuotientGroup.ker_mk'] using hker

private theorem criticalDistance_two_coreResidual_le_vertexModule_of_shift
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' u : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : criticalDistance S = 2)
    (hshiftCrit : IsCriticalPair S u a)
    (hgen : edgeTwoCore S u a ⊔ vertexZ S a' = stabilizer S a) :
    ⁅pCore 2 (stabilizer S a),
      twoResidualAmbient (⊤ : Subgroup (stabilizer S a))⁆ ≤
        vertexModule S a := by
  classical
  have hbpos : 0 < criticalDistance S := by omega
  obtain ⟨hVa, ha'Ga, hdataAA'⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA a a' hcrit hbpos
  have hcritA'A : IsCriticalPair S a' a :=
    hdataAA'.critical.reverse_critical
  obtain ⟨_hVa', _haGa', hslA'A⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA a' a hcritA'A hbpos
  obtain ⟨_hVu, _haGu, hdataUA⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA u a hshiftCrit hbpos
  obtain ⟨_hVu', _haGu', hslUA⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA u a hshiftCrit hbpos
  have hcritAU : IsCriticalPair S a u :=
    hdataUA.critical.reverse_critical
  obtain ⟨_hVa2, huGa, hslAU⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA a u hcritAU hbpos
  have hdistAA' : (cosetGraph S).dist a a' = 2 := by
    rw [hcrit.2.1, hb]
  have hdistAU : (cosetGraph S).dist a u = 2 := by
    rw [hcritAU.2.1, hb]
  have hQaEdgeA' : vertexTwoCore S a ≤ edgeTwoCore S a' a :=
    vertexTwoCore_le_endpointEdgeCore_of_dist_two
      S T hTS a a' hcrit.1 hcritA'A.1 hdistAA'
  have hQaGa' : vertexTwoCore S a ≤ stabilizer S a' :=
    hQaEdgeA'.trans (edgeTwoCore_le_leftStabilizer S a' a)
  have hQaEdgeU : vertexTwoCore S a ≤ edgeTwoCore S u a :=
    vertexTwoCore_le_endpointEdgeCore_of_dist_two
      S T hTS a u hcrit.1 hshiftCrit.1 hdistAU
  have hQaGu : vertexTwoCore S a ≤ stabilizer S u :=
    hQaEdgeU.trans (edgeTwoCore_le_leftStabilizer S u a)
  have hQa'Edge : vertexTwoCore S a' ≤ edgeTwoCore S a a' :=
    vertexTwoCore_le_endpointEdgeCore_of_dist_two S T hTS a' a
      hcritA'A.1 hcrit.1 (by simpa [SimpleGraph.dist_comm] using hdistAA')
  have hQa'Ga : vertexTwoCore S a' ≤ stabilizer S a :=
    hQa'Edge.trans (edgeTwoCore_le_leftStabilizer S a a')
  have hQuEdge : vertexTwoCore S u ≤ edgeTwoCore S a u :=
    vertexTwoCore_le_endpointEdgeCore_of_dist_two S T hTS u a
      hshiftCrit.1 hcrit.1 (by simpa [SimpleGraph.dist_comm] using hdistAU)
  have hQuGa : vertexTwoCore S u ≤ stabilizer S a :=
    hQuEdge.trans (edgeTwoCore_le_leftStabilizer S a u)
  have hZaQa : vertexZ S a ≤ vertexTwoCore S a :=
    hdataAA'.left_Z_le_coreOmega.trans
      (omegaOneCenterAmbient_le (vertexTwoCore S a))
  have hZa'Qa' : vertexZ S a' ≤ vertexTwoCore S a' :=
    hdataAA'.right_Z_le_coreOmega.trans
      (omegaOneCenterAmbient_le (vertexTwoCore S a'))
  have hZuQu : vertexZ S u ≤ vertexTwoCore S u :=
    hdataUA.left_Z_le_coreOmega.trans
      (omegaOneCenterAmbient_le (vertexTwoCore S u))
  have hQaSourceA' :
      vertexTwoCore S a ≤ vertexZ S a ⊔ vertexTwoCore S a' :=
    le_reverse_sourceSylow S a a' (vertexTwoCore S a) hQaGa'
      (vertexTwoCore_isPGroup S a) hZaQa hslA'A.sourceSylow
  have hQaSourceU :
      vertexTwoCore S a ≤ vertexZ S a ⊔ vertexTwoCore S u :=
    le_reverse_sourceSylow S a u (vertexTwoCore S a) hQaGu
      (vertexTwoCore_isPGroup S a) hZaQa hslUA.sourceSylow
  have hZuEdge : vertexZ S u ≤ edgeTwoCore S u a := by
    rw [← edgeTwoCore_comm S a u]
    exact hZuQu.trans hQuEdge
  have hEleGa : edgeTwoCore S u a ≤ vertexZ S u ⊔ vertexTwoCore S a :=
    le_reverse_sourceSylow S u a (edgeTwoCore S u a)
      (edgeTwoCore_le_rightStabilizer S u a)
      (edgeTwoCore_isPGroup S u a) hZuEdge hslAU.sourceSylow
  let G := stabilizer S a
  let Q : Subgroup G := pCore 2 G
  let Z : Subgroup G := (vertexZ S a).subgroupOf G
  let A' : Subgroup G := (vertexZ S a').subgroupOf G
  let U : Subgroup G := (vertexZ S u).subgroupOf G
  let Q' : Subgroup G := (vertexTwoCore S a').subgroupOf G
  let Qu : Subgroup G := (vertexTwoCore S u).subgroupOf G
  let F : Subgroup G := A' ⊔ U
  have hQmap : Q.map G.subtype = vertexTwoCore S a := rfl
  have hZmap : Z.map G.subtype = vertexZ S a := by
    exact Subgroup.map_subgroupOf_eq_of_le (vertexZ_le_stabilizer S a)
  have hA'map : A'.map G.subtype = vertexZ S a' := by
    exact Subgroup.map_subgroupOf_eq_of_le ha'Ga
  have hUmap : U.map G.subtype = vertexZ S u := by
    exact Subgroup.map_subgroupOf_eq_of_le huGa
  have hQ'map : Q'.map G.subtype = vertexTwoCore S a' := by
    exact Subgroup.map_subgroupOf_eq_of_le hQa'Ga
  have hQumap : Qu.map G.subtype = vertexTwoCore S u := by
    exact Subgroup.map_subgroupOf_eq_of_le hQuGa
  have hQSourceA' : Q ≤ Q' ⊔ Z := by
    rw [← Subgroup.map_le_map_iff_of_injective G.subtype_injective]
    rw [Subgroup.map_sup, hQmap, hQ'map, hZmap]
    simpa [sup_comm] using hQaSourceA'
  have hQSourceU : Q ≤ Qu ⊔ Z := by
    rw [← Subgroup.map_le_map_iff_of_injective G.subtype_injective]
    rw [Subgroup.map_sup, hQmap, hQumap, hZmap]
    simpa [sup_comm] using hQaSourceU
  have hQ'centA' : Q' ≤ Subgroup.centralizer (A' : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply G.subtype_injective
    have hzOmega := hdataAA'.right_Z_le_coreOmega (show (z : FreeAmalgam S) ∈
      vertexZ S a' from hz)
    exact ((mem_omegaOneCenterAmbient_iff (vertexTwoCore S a')
      (z : FreeAmalgam S)).mp hzOmega |>.2.2 (q : FreeAmalgam S) hq).symm
  have hQucentU : Qu ≤ Subgroup.centralizer (U : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply G.subtype_injective
    have hzOmega := hdataUA.left_Z_le_coreOmega (show (z : FreeAmalgam S) ∈
      vertexZ S u from hz)
    exact ((mem_omegaOneCenterAmbient_iff (vertexTwoCore S u)
      (z : FreeAmalgam S)).mp hzOmega |>.2.2 (q : FreeAmalgam S) hq).symm
  have hZnormal : Z.Normal := by
    simpa [Z, G] using vertexZ_normal_stabilizer S a
  have hQA' : ⁅Q, A'⁆ ≤ Z :=
    commutator_le_of_source_sylow Q A' Q' Z hZnormal
      hQSourceA' hQ'centA'
  have hQU : ⁅Q, U⁆ ≤ Z :=
    commutator_le_of_source_sylow Q U Qu Z hZnormal
      hQSourceU hQucentU
  have hQF : ⁅Q, F⁆ ≤ Z := by
    simpa [F] using commutator_sup_le_of_each Q A' U Z hZnormal hQA' hQU
  have hFQamb :
      (vertexZ S a' ⊔ vertexZ S u) ⊔ vertexTwoCore S a =
        stabilizer S a := by
    apply le_antisymm
    · exact sup_le (sup_le ha'Ga huGa)
        (by
          unfold vertexTwoCore twoCoreAmbient
          exact Subgroup.map_subtype_le _)
    · rw [← hgen]
      refine sup_le ?_ (le_sup_left.trans le_sup_left)
      exact hEleGa.trans
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hFQ : F ⊔ Q = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup,
      show (⊤ : Subgroup G).map G.subtype = G by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype],
      show F.map G.subtype = vertexZ S a' ⊔ vertexZ S u by
        simp only [F, Subgroup.map_sup, hA'map, hUmap], hQmap]
    exact hFQamb
  have hQ2 : IsPGroup 2 Q := pCore_isPGroup
  have hlocal : ⁅Q, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ Z :=
    residual_commutator_le_of_generated_modulo Q F Z hZnormal hQ2 hQF hFQ
  have hZeq : Z = vertexModule S a := by
    apply Subgroup.map_injective G.subtype_injective
    rw [hZmap]
    simpa [G, vertexModule, vertexSylow, VertexGroup] using
      (vertexZ_eq_local_vSubgroup S a).symm
  rw [hZeq] at hlocal
  simpa [G, Q] using hlocal


/-- At critical distance two, the local residual commutator is contained in
the canonical local module. -/
public theorem criticalDistance_two_coreResidual_le_vertexModule
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : criticalDistance S = 2) :
    ⁅pCore 2 (stabilizer S a),
      twoResidualAmbient (⊤ : Subgroup (stabilizer S a))⁆ ≤
        vertexModule S a := by
  have hbpos : 0 < criticalDistance S := by omega
  let hframe : DistanceTwoShift.Frame S a a' a :=
    { left_length := by simp [hb]
      right_length := by simpa [hb] using hcrit.2.1 }
  obtain ⟨u, hu⟩ :=
    criticalPair_distanceTwoShift
      S T hTS hP hSne hA a a' hcrit hbpos a hframe
  exact criticalDistance_two_coreResidual_le_vertexModule_of_shift
    S T hTS hP hSne hA a a' u hcrit hb
      hu.shifted_critical hu.generates_left_stabilizer

end Stellmacher.PushingUp
