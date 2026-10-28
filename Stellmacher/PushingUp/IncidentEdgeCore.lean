module

public import Stellmacher.PushingUp.CriticalDistanceBasic

/-!
# The two-core of an incident M-side edge

This module isolates the graph-local edge calculation used in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), (1.1)(d) and (1.3).  If `a` is in the
M-vertex orbit and `d` is adjacent to `a`, then the edge stabilizer
`G_a ∩ G_d` is itself a Sylow 2-subgroup of `G_a`.  Consequently its
2-core is the whole edge stabilizer.

The proof transports the distinguished base Sylow through an element carrying
the base edge to `(a,d)`, identifies its ambient image with the transported
edge stabilizer, and uses that a 2-group equals its own 2-core.  All base-edge
and transport machinery remains private.  The result has no condition (P),
critical-pair hypothesis, or finiteness assumption on the free amalgam or its
vertex set.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private def baseMHom (S : Subgroup M) :
    M →* stabilizer S (mVertex S 1) :=
  (embedM S).codRestrict _ (fun m ↦ by
    rw [stabilizer_m_base]
    exact ⟨m, rfl⟩)

private theorem baseMHom_injective (S : Subgroup M) :
    Function.Injective (baseMHom S) := by
  intro x y hxy
  apply embedM_injective S
  exact congrArg Subtype.val hxy

private theorem baseMHom_surjective (S : Subgroup M) :
    Function.Surjective (baseMHom S) := by
  intro y
  have hy : (y : FreeAmalgam S) ∈ Mbar S := by
    rw [← stabilizer_m_base]
    exact y.property
  obtain ⟨m, hm⟩ := hy
  refine ⟨m, Subtype.ext ?_⟩
  exact hm

private noncomputable def baseSylow [Finite M] (S : Subgroup M)
    (T : Sylow 2 M) : Sylow 2 (stabilizer S (mVertex S 1)) :=
  Sylow.mapSurjective (baseMHom_surjective S) T

private theorem baseSylow_ambient_eq_Sbar [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S) :
    sylowAt S (mVertex S 1) (baseSylow S T) = Sbar S := by
  unfold sylowAt baseSylow
  rw [Sylow.coe_mapSurjective (baseMHom_surjective S) T,
    Subgroup.map_map]
  change (T : Subgroup M).map (embedM S) = Sbar S
  rw [hTS]
  calc
    S.map (embedM S) =
        ((⊤ : Subgroup S).map S.subtype).map (embedM S) := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (⊤ : Subgroup S).map ((embedM S).comp S.subtype) :=
      Subgroup.map_map _ _ _
    _ = (⊤ : Subgroup S).map (embedS S) := by rw [embedM_comp_subtype]
    _ = Sbar S := by
      rw [← MonoidHom.range_eq_map]
      rfl

private theorem exists_action_base_edge [Finite M]
    (S : Subgroup M) (a d : Vertex S)
    (ha : InMVertexOrbit S a) (had : Adjacent S a d) :
    ∃ g : FreeAmalgam S,
      a = act S g (mVertex S 1) ∧ d = act S g (hVertex S 1) := by
  obtain ⟨x, hax⟩ := ha
  have hae : Adjacent S a (act S x (hVertex S 1)) := by
    rw [hax]
    exact (adjacent_act_iff S x (mVertex S 1) (hVertex S 1)).2
      (base_adjacent S)
  obtain ⟨y, hya, hyd⟩ :=
    stabilizer_transitive_neighbors S a hae had
  refine ⟨x * y, ?_, ?_⟩
  · rw [act_mul, ← hax]
    exact hya.symm
  · rw [act_mul]
    exact hyd.symm

private noncomputable def stabilizerActEquiv (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    stabilizer S d ≃* stabilizer S (act S g d) :=
  ((MulAut.conj g⁻¹).subgroupMap (stabilizer S d)).trans
    (MulEquiv.subgroupCongr (stabilizer_act S g d).symm)

private theorem transportedSylow_ambient [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (g : FreeAmalgam S) :
    let e := stabilizerActEquiv S g (mVertex S 1)
    let he : Function.Surjective e.toMonoidHom := e.surjective
    let Tg : Sylow 2 (stabilizer S (act S g (mVertex S 1))) :=
      (baseSylow S T).mapSurjective (f := e.toMonoidHom) he
    sylowAt S (act S g (mVertex S 1)) Tg =
      (sylowAt S (mVertex S 1) (baseSylow S T)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  dsimp only
  unfold sylowAt
  change
    (((baseSylow S T : Sylow 2 (stabilizer S (mVertex S 1))) :
        Subgroup (stabilizer S (mVertex S 1))).map
          (stabilizerActEquiv S g (mVertex S 1)).toMonoidHom).map
            (stabilizer S (act S g (mVertex S 1))).subtype =
      (((baseSylow S T : Sylow 2 (stabilizer S (mVertex S 1))) :
        Subgroup (stabilizer S (mVertex S 1))).map
          (stabilizer S (mVertex S 1)).subtype).map
            (MulAut.conj g⁻¹).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem edgeStabilizer_eq_sylowAt [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a d : Vertex S) (ha : InMVertexOrbit S a) (had : Adjacent S a d) :
    ∃ Ta : Sylow 2 (stabilizer S a),
      stabilizer S a ⊓ stabilizer S d = sylowAt S a Ta := by
  classical
  obtain ⟨g, rfl, rfl⟩ := exists_action_base_edge S a d ha had
  let e := stabilizerActEquiv S g (mVertex S 1)
  let he : Function.Surjective e.toMonoidHom := e.surjective
  let Tg : Sylow 2 (stabilizer S (act S g (mVertex S 1))) :=
    (baseSylow S T).mapSurjective (f := e.toMonoidHom) he
  refine ⟨Tg, ?_⟩
  let c : FreeAmalgam S ≃* FreeAmalgam S := MulAut.conj g⁻¹
  calc
    stabilizer S (act S g (mVertex S 1)) ⊓
        stabilizer S (act S g (hVertex S 1)) =
      (stabilizer S (mVertex S 1) ⊓ stabilizer S (hVertex S 1)).map
        c.toMonoidHom := by
          rw [stabilizer_act, stabilizer_act,
            Subgroup.map_inf _ _ c.toMonoidHom c.injective]
    _ = (Sbar S).map c.toMonoidHom := by rw [base_edge_stabilizer]
    _ = (sylowAt S (mVertex S 1) (baseSylow S T)).map
        c.toMonoidHom := by
      rw [baseSylow_ambient_eq_Sbar S T hTS]
    _ = sylowAt S (act S g (mVertex S 1)) Tg := by
      exact (transportedSylow_ambient S T g).symm

private theorem twoCoreAmbient_eq_self_of_isPGroup
    {G : Type*} [Group G] (H : Subgroup G) (hHp : IsPGroup 2 H) :
    twoCoreAmbient H = H := by
  have htopP : IsPGroup 2 (⊤ : Subgroup H) := hHp.to_subgroup ⊤
  have hcoreTop : pCore 2 H = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, htopP⟩
  unfold twoCoreAmbient
  rw [hcoreTop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- An edge incident to an M-orbit vertex is a 2-group, so its ambient
2-core is the whole edge stabilizer. -/
public theorem incident_edgeTwoCore_eq_edgeStabilizer [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a d : Vertex S) (ha : InMVertexOrbit S a)
    (had : Adjacent S a d) :
    edgeTwoCore S a d = stabilizer S a ⊓ stabilizer S d := by
  obtain ⟨Ta, hEdge⟩ := edgeStabilizer_eq_sylowAt S T hTS a d ha had
  unfold edgeTwoCore
  exact twoCoreAmbient_eq_self_of_isPGroup _ (by
    rw [hEdge]
    unfold sylowAt
    exact Ta.isPGroup'.map (stabilizer S a).subtype)

end Stellmacher.PushingUp
