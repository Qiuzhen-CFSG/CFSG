module

public import Stellmacher.PushingUp.CriticalPairActionInputs
public import Stellmacher.PushingUp.IncidentEdgeCore

/-!
# Normality of the core intersection in a distance-two shift

For two M-orbit vertices `a` and `u` at distance two, suppose the join
`W = Z_a ⊔ Z_u` is contained and normal in `G_u`. Under the positive-distance
pushing-up hypotheses and the nested `SL₂(2)` hypothesis, this module proves
that `Q_a ∩ Q_u` is normal in `G_u`. This is the second normality assertion
of Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.4), step (3), p. 13.
The critical-distance-bound proof supplies the normality of `W` separately.

The proof identifies the intersection with `Q_u ∩ C_{G_u}(W)`. Each core
centralizes its own vertex center, giving one inclusion. Conversely, the
local kernel along a path of length two places `Q_u` in `G_a`. Hence
`Q_u ∩ C_{G_u}(W)` is a 2-subgroup of `G_a` centralizing `Z_a`; the odd index
of `Q_a` in that centralizer, from (1.4)(a), forces it into `Q_a`. Both
factors of the resulting internal intersection are normal in `G_u`.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u
variable {M : Type u} [Group M] [Finite M]

private theorem core_le_stabilizer_of_dist_two
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x y : Vertex S) (hx : InMVertexOrbit S x)
    (hxy : (cosetGraph S).dist x y = 2) :
    vertexTwoCore S x ≤ stabilizer S y := by
  have hed : (cosetGraph S).edist x y = 2 := by
    rw [← (cosetGraph_connected S x y).coe_dist_eq_edist, hxy]
    rfl
  obtain ⟨d, hd⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  have hxd : Adjacent S x d :=
    (cosetGraph_adj S x d).mp hd.1
  have hdy : Adjacent S d y :=
    adjacent_symm S ((cosetGraph_adj S y d).mp hd.2)
  have hlocal := localKernel_at_mEdge S T hTS x d hx hxd
  have hQK : vertexTwoCore S x ≤ neighborhoodKernel S x := by
    obtain ⟨P, hP⟩ := hlocal.1
    rw [← hP]
    exact Subgroup.map_subtype_le _
  have hQE : vertexTwoCore S x ≤ edgeTwoCore S x d := by
    rw [incident_edgeTwoCore_eq_edgeStabilizer S T hTS x d hx hxd]
    intro g hg
    exact ⟨(hQK hg).1, (hQK hg).2 d hxd⟩
  intro g hg
  exact (hlocal.2.2.2 (hQE hg)).2 y hdy

omit [Finite M] in
private theorem core_le_ambientCentralizer
    (S : Subgroup M) (a : Vertex S)
    (hodd : CriticalVertexCentralizer.Conclusion S a) :
    vertexTwoCore S a ≤ Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_vertexCentralizerLocal_iff S a x).mp (hodd.core_le_centralizer hx)

/-- A normal join of the two vertex centers makes the shared two-core
normal in the shifted vertex stabilizer. -/
public theorem shift_coreIntersection_normal_of_centerJoin_normal
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a u : Vertex S) (ha : InMVertexOrbit S a) (hu : InMVertexOrbit S u)
    (hb : 0 < criticalDistance S)
    (hau : (cosetGraph S).dist a u = 2)
    (hWGu : vertexZ S a ⊔ vertexZ S u ≤ stabilizer S u)
    (hWnormal : ((vertexZ S a ⊔ vertexZ S u).subgroupOf
      (stabilizer S u)).Normal) :
    ((vertexTwoCore S a ⊓ vertexTwoCore S u).subgroupOf
      (stabilizer S u)).Normal := by
  let Ga := stabilizer S a
  let Gu := stabilizer S u
  let W : Subgroup Gu := (vertexZ S a ⊔ vertexZ S u).subgroupOf Gu
  let _ : W.Normal := hWnormal
  let N : Subgroup Gu := pCore 2 Gu ⊓ Subgroup.centralizer (W : Set Gu)
  let A : Subgroup (FreeAmalgam S) := N.map Gu.subtype
  have odd (x : Vertex S) (hx : InMVertexOrbit S x) :
      CriticalVertexCentralizer.Conclusion S x := by
    have hNested := stabilizer_isSL2Two_nested_of_mOrbit S x hx hA
    have hres : HasMinimalFrattiniResidual S x := by
      simpa [HasMinimalFrattiniResidual, vertexFrattiniResidual,
        VertexFrattiniQuotient, VertexCoreQuotient] using
          sl2Two_twoResidual_isMinimalNormal hNested
    exact criticalVertex_centralizer_oddIndex T hTS hP hSne x hx hb hres
  have hoddA := odd a ha
  have hoddU := odd u hu
  have hQuGa : vertexTwoCore S u ≤ Ga :=
    core_le_stabilizer_of_dist_two S T hTS u a hu (by
      simpa [SimpleGraph.dist_comm] using hau)
  have hAQu : A ≤ vertexTwoCore S u :=
    Subgroup.map_mono (show N ≤ pCore 2 Gu from inf_le_left)
  have hAGa : A ≤ Ga := hAQu.trans hQuGa
  have hA2 : IsPGroup 2 A :=
    ((pCore_isPGroup (p := 2) (G := Gu)).to_le
      (show N ≤ pCore 2 Gu from inf_le_left)).map Gu.subtype
  have hAcent : A ≤ Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzWambient : z ∈ vertexZ S a ⊔ vertexZ S u :=
      (le_sup_left : vertexZ S a ≤ vertexZ S a ⊔ vertexZ S u) hz
    let zU : Gu := ⟨z, hWGu hzWambient⟩
    have hzW : zU ∈ W := hzWambient
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx.2) zU hzW)
  have hAcore : A ≤ vertexTwoCore S a := by
    have hA2local : IsPGroup 2 (A.subgroupOf Ga) :=
      hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAGa).symm
    have hAC : A.subgroupOf Ga ≤ vertexCentralizerLocal S a := by
      intro x hx
      exact (mem_vertexCentralizerLocal_iff S a x).mpr (hAcent hx)
    have hle := hA2local.le_pCore_of_le_oddIndexOverCore
      hoddA.core_le_centralizer hoddA.centralizer_mod_core_odd hAC
    intro x hx
    exact Subgroup.mem_map_of_mem Ga.subtype
      (hle (show (⟨x, hAGa hx⟩ : Ga) ∈ A.subgroupOf Ga from hx))
  have heq : (vertexTwoCore S a ⊓ vertexTwoCore S u).subgroupOf Gu = N := by
    apply le_antisymm
    · intro x hx
      have hxCore : x ∈ pCore 2 Gu := by
        obtain ⟨q, hq, hqx⟩ := hx.2
        have hqx' : q = x := Subtype.ext hqx
        rwa [← hqx']
      refine ⟨hxCore, ?_⟩
      have hxZa := core_le_ambientCentralizer S a hoddA hx.1
      have hxZu := core_le_ambientCentralizer S u hoddU hx.2
      have hxW : (x : FreeAmalgam S) ∈ Subgroup.centralizer
          ((vertexZ S a ⊔ vertexZ S u : Subgroup (FreeAmalgam S)) : Set _) := by
        rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
          Subgroup.mem_centralizer_iff]
        intro z hz
        rcases hz with hz | hz
        · exact Subgroup.mem_centralizer_iff.mp hxZa z hz
        · exact Subgroup.mem_centralizer_iff.mp hxZu z hz
      change x ∈ Subgroup.centralizer (W : Set Gu)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxW z hz)
    · intro x hx
      have hxA : (x : FreeAmalgam S) ∈ A :=
        Subgroup.mem_map_of_mem Gu.subtype hx
      exact ⟨hAcore hxA, hAQu hxA⟩
  rw [heq]
  infer_instance

end Stellmacher.PushingUp
