module

public import Stellmacher.PushingUp.CriticalPairSL2Two
public import Stellmacher.SectionTwo.NestedSL2TwoGeneration

/-!
# A generating predecessor edge for a critical pair

This module proves the first, generating-edge step of Stellmacher, *Pushing
up*, Arch. Math. 46 (1986), proof of (2.3), journal p.12.  For a positive
critical pair `(a,a')`, it chooses a neighbor `aMinusOne` of `a` whose edge
2-core together with `Z_(a')` generates the full vertex stabilizer `G_a`.

The proof starts from `criticalPair_sl2Two`: internally in `G_a`, the subgroup
`Z_(a') O₂(G_a)` is Sylow and the quotient by `O₂(G_a)` and its Frattini
subgroup is `SL₂(2)`.  A moved Sylow subgroup in this order-six quotient,
lifted twice through the quotient maps, generates with `Z_(a')`; Frattini
nongeneration removes the intermediate Frattini subgroup.  Finally, Sylow
conjugacy and the free-amalgam edge transport realize that lifted Sylow as the
2-core of an edge incident to `a`.  The finite-group generation step is supplied by
`SectionTwo.NestedSL2TwoGeneration`; edge-transport helpers stay private. No
finiteness assumption on the graph's vertex set is used.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private theorem sylowAt_smul (S : Subgroup M) (d : Vertex S)
    (x : stabilizer S d) (Td : Sylow 2 (stabilizer S d)) :
    sylowAt S d (x • Td) =
      (sylowAt S d Td).map
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by
  unfold sylowAt
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  change (((Td : Sylow 2 (stabilizer S d)) : Subgroup (stabilizer S d)).map
      (MulAut.conj x).toMonoidHom).map (stabilizer S d).subtype =
    (((Td : Sylow 2 (stabilizer S d)) : Subgroup (stabilizer S d)).map
      (stabilizer S d).subtype).map
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

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

private noncomputable def baseMEquiv (S : Subgroup M) :
    M ≃* stabilizer S (mVertex S 1) :=
  MulEquiv.ofBijective (baseMHom S)
    ⟨baseMHom_injective S, baseMHom_surjective S⟩

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
    (S : Subgroup M) (a b : Vertex S)
    (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    ∃ g : FreeAmalgam S,
      a = act S g (mVertex S 1) ∧ b = act S g (hVertex S 1) := by
  obtain ⟨x, hax⟩ := ha
  have hae : Adjacent S a (act S x (hVertex S 1)) := by
    rw [hax]
    exact (adjacent_act_iff S x (mVertex S 1) (hVertex S 1)).2
      (base_adjacent S)
  obtain ⟨y, hya, hyb⟩ := stabilizer_transitive_neighbors S a hae hab
  refine ⟨x * y, ?_, ?_⟩
  · rw [act_mul, ← hax]
    exact hya.symm
  · rw [act_mul]
    exact hyb.symm

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
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    ∃ Ta : Sylow 2 (stabilizer S a),
      stabilizer S a ⊓ stabilizer S b = sylowAt S a Ta := by
  classical
  obtain ⟨g, rfl, rfl⟩ := exists_action_base_edge S a b ha hab
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
    _ = (sylowAt S (mVertex S 1) (baseSylow S T)).map c.toMonoidHom := by
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

private theorem edgeTwoCore_eq_edgeStabilizer [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    edgeTwoCore S a b = stabilizer S a ⊓ stabilizer S b := by
  obtain ⟨Ta, hEdge⟩ := edgeStabilizer_eq_sylowAt S T hTS a b ha hab
  unfold edgeTwoCore
  exact twoCoreAmbient_eq_self_of_isPGroup _ (by
    rw [hEdge]
    unfold sylowAt
    exact Ta.isPGroup'.map (stabilizer S a).subtype)

private theorem map_internal_ambient
    {G : Type u} [Group G]
    (P : Subgroup G) (e : G ≃* G) (K : Subgroup P) :
    (K.map (e.subgroupMap P : P →* P.map (e : G →* G))).map
        (P.map (e : G →* G)).subtype =
      (K.map P.subtype).map (e : G →* G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem twoCoreAmbient_map_equiv
    {G : Type u} [Group G] (e : G ≃* G) (P : Subgroup G) :
    twoCoreAmbient (P.map (e : G →* G)) =
      (twoCoreAmbient P).map (e : G →* G) := by
  let eP : P ≃* P.map (e : G →* G) := e.subgroupMap P
  have hcore : (pCore 2 P).map (eP : P →* P.map (e : G →* G)) =
      pCore 2 (P.map (e : G →* G)) := pCore_map_iso 2 eP
  unfold twoCoreAmbient
  rw [← hcore, map_internal_ambient]

private theorem edgeTwoCore_act (S : Subgroup M)
    (g : FreeAmalgam S) (d e : Vertex S) :
    edgeTwoCore S (act S g d) (act S g e) =
      (edgeTwoCore S d e).map (MulAut.conj g⁻¹).toMonoidHom := by
  let c : FreeAmalgam S ≃* FreeAmalgam S := MulAut.conj g⁻¹
  unfold edgeTwoCore
  rw [stabilizer_act, stabilizer_act]
  calc
    twoCoreAmbient
        ((stabilizer S d).map (c : FreeAmalgam S →* FreeAmalgam S) ⊓
          (stabilizer S e).map (c : FreeAmalgam S →* FreeAmalgam S)) =
      twoCoreAmbient ((stabilizer S d ⊓ stabilizer S e).map
        (c : FreeAmalgam S →* FreeAmalgam S)) := by
          rw [Subgroup.map_inf _ _ (c : FreeAmalgam S →* FreeAmalgam S) c.injective]
    _ = (twoCoreAmbient (stabilizer S d ⊓ stabilizer S e)).map
        (c : FreeAmalgam S →* FreeAmalgam S) := twoCoreAmbient_map_equiv c _

private theorem exists_incident_edgeTwoCore_eq_sylowAt [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (P : Sylow 2 (stabilizer S a)) :
    ∃ b : Vertex S, Adjacent S a b ∧ edgeTwoCore S a b = sylowAt S a P := by
  classical
  have haOrbit := ha
  obtain ⟨g, hag⟩ := ha
  let b₀ : Vertex S := act S g (hVertex S 1)
  have hab₀ : Adjacent S a b₀ := by
    rw [hag]
    exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2 (base_adjacent S)
  obtain ⟨R, hEdge⟩ := edgeStabilizer_eq_sylowAt S T hTS a b₀ haOrbit hab₀
  have hCore : edgeTwoCore S a b₀ = sylowAt S a R :=
    (edgeTwoCore_eq_edgeStabilizer S T hTS a b₀ haOrbit hab₀).trans hEdge
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (stabilizer S a) R P
  have hxfix : act S (x : FreeAmalgam S) a = a := x.property
  have hxinvfix : act S (x : FreeAmalgam S)⁻¹ a = a := by
    calc
      act S (x : FreeAmalgam S)⁻¹ a =
          act S (x : FreeAmalgam S)⁻¹
            (act S (x : FreeAmalgam S) a) := by rw [hxfix]
      _ = a := by rw [← act_mul]; simp
  let b : Vertex S := act S (x : FreeAmalgam S)⁻¹ b₀
  refine ⟨b, ?_, ?_⟩
  · have := (adjacent_act_iff S (x : FreeAmalgam S)⁻¹ a b₀).2 hab₀
    simpa [b, hxinvfix] using this
  · have hmap := edgeTwoCore_act S (x : FreeAmalgam S)⁻¹ a b₀
    rw [hxinvfix] at hmap
    calc
      edgeTwoCore S a b =
          (edgeTwoCore S a b₀).map
            (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by
              simpa [b] using hmap
      _ = (sylowAt S a R).map
          (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by rw [hCore]
      _ = sylowAt S a (x • R) := (sylowAt_smul S a x R).symm
      _ = sylowAt S a P := by rw [hx]

public theorem criticalPair_generatingPredecessor [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S) :
    ∃ aMinusOne : Vertex S,
      Adjacent S a aMinusOne ∧
        edgeTwoCore S a aMinusOne ⊔ vertexZ S a' = stabilizer S a := by
  classical
  obtain ⟨hV, ha', hSL2⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA a a' hcrit hb
  obtain ⟨R, hR⟩ := hSL2.sourceSylow
  let A : Subgroup (stabilizer S a) :=
    (vertexZ S a').subgroupOf (stabilizer S a)
  have hAR : A ⊔ pCore 2 (stabilizer S a) =
      (R : Subgroup (stabilizer S a)) := by
    apply Subgroup.map_injective (stabilizer S a).subtype_injective
    rw [Subgroup.map_sup]
    rw [Subgroup.map_subgroupOf_eq_of_le ha']
    simpa only [vertexTwoCore, twoCoreAmbient, sylowAt] using hR.symm
  have hNested :=
    stabilizer_isSL2Two_nested_of_mOrbit S a hcrit.1 hA
  obtain ⟨P, hAP⟩ :=
    SectionTwo.exists_sylow_sup_eq_top_of_nestedSL2Two A R hAR hNested
  obtain ⟨aMinusOne, haaMinusOne, hEdgeP⟩ :=
    exists_incident_edgeTwoCore_eq_sylowAt S T hTS a hcrit.1 P
  refine ⟨aMinusOne, haaMinusOne, ?_⟩
  calc
    edgeTwoCore S a aMinusOne ⊔ vertexZ S a' =
        sylowAt S a P ⊔ vertexZ S a' := by rw [hEdgeP]
    _ = ((P : Subgroup (stabilizer S a)) ⊔ A).map
        (stabilizer S a).subtype := by
          rw [Subgroup.map_sup]
          change sylowAt S a P ⊔ vertexZ S a' =
            sylowAt S a P ⊔ A.map (stabilizer S a).subtype
          rw [Subgroup.map_subgroupOf_eq_of_le ha']
    _ = (A ⊔ (P : Subgroup (stabilizer S a))).map
        (stabilizer S a).subtype := by rw [sup_comm]
    _ = (⊤ : Subgroup (stabilizer S a)).map
        (stabilizer S a).subtype := by rw [hAP]
    _ = stabilizer S a := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Stellmacher.PushingUp
