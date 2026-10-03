module

public import Stellmacher.PushingUp.LocalKernelEdge
public import Stellmacher.OmegaOneCenterMap

/-!
# Critical distance in the free-amalgam graph

This module proves Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma
(1.3), in the specialized amalgam with `B = S` and `A = Aut(S)`.  It defines
the Sylow-center subgroup `Z_d`, the set of distances where the base `Z`
escapes a pointwise neighborhood kernel, its minimum `b`, and critical pairs.
The theorem packages the source's five conclusions: the two local kernel
facts, parity of `b`, non-equality of `Z_d` with any one Sylow center, and the
containment `Z_d ≤ Omega_1(Z(Q_d))` unless `b = 0`.

The vertex set is generally infinite.  Nontriviality of `S`, together with
condition (P), makes the critical-distance set nonempty through faithfulness
of the amalgam action; `Nat.sInf_mem` then supplies an attained minimum without
any finiteness assumption on vertices.  Conjugation transports stabilizers,
local kernels, Sylow subgroups, and `Z_d`.  A shortest path and the bipartite
coloring force the minimum to be even.  For the Sylow-center inequality, a
chosen Sylow subgroup is conjugated to the Sylow subgroup carried by an
adjacent edge; normality on both endpoint stabilizers would contradict the
no-common-invariant conclusion of (1.2).  Finally, positive even minimum and
minimality place every Sylow-center generator centrally in `Q_d`.

The local assertions (1.3)(a),(b) are imported from `LocalKernelEdge`; the
transport proofs remain private, while their distance and vertex-center
equations are exported for translated paths in (2.4). The M-side kernel is
also identified publicly with its vertex 2-core. The public
minimum API records the two consequences reused by later distance arguments:
strictly shorter M-side centers lie in the target neighborhood kernel, and an
attained critical pair exists from every M-side vertex.  The finite-stabilizer
instance and the containment and relative normality of `Z_d` in its vertex
stabilizer form the remaining small public local-data API.
The public incident-edge Sylow wrapper also supports the two-Sylow
generation arguments at positive critical distance. The existence of an
isomorphism from `M` to any M-side stabilizer supports transport of the
standing local hypotheses without exposing the chosen equivalence.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

/-- A Sylow subgroup of a vertex stabilizer, mapped into the free amalgam. -/
@[expose] public noncomputable def sylowAt (S : Subgroup M) (d : Vertex S)
    (T : Sylow 2 (stabilizer S d)) : Subgroup (FreeAmalgam S) :=
  (T : Subgroup (stabilizer S d)).map (stabilizer S d).subtype

/-- The subgroup `Omega_1(Z(T))`, mapped into the free amalgam. -/
@[expose] public noncomputable def sylowOmegaAt (S : Subgroup M) (d : Vertex S)
    (T : Sylow 2 (stabilizer S d)) : Subgroup (FreeAmalgam S) :=
  omegaOneCenterAmbient (sylowAt S d T)

/-- The source's `Z_d`, generated over all Sylow 2-subgroups of `G_d`. -/
@[expose] public noncomputable def vertexZ (S : Subgroup M) (d : Vertex S) :
    Subgroup (FreeAmalgam S) :=
  sSup {Z : Subgroup (FreeAmalgam S) |
    ∃ T : Sylow 2 (stabilizer S d), Z = sylowOmegaAt S d T}

/-- Distances from the fixed base vertex at which its `Z` escapes a local kernel. -/
@[expose] public def criticalDistanceSet (S : Subgroup M) : Set ℕ :=
  {n | ∃ d' : Vertex S,
    (cosetGraph S).dist (mVertex S 1) d' = n ∧
      ¬ vertexZ S (mVertex S 1) ≤ neighborhoodKernel S d'}

/-- The source's minimum critical distance. -/
@[expose] public noncomputable def criticalDistance (S : Subgroup M) : ℕ :=
  sInf (criticalDistanceSet S)

/-- A source-faithful critical pair. -/
@[expose] public def IsCriticalPair (S : Subgroup M) (a a' : Vertex S) : Prop :=
  InMVertexOrbit S a ∧
    (cosetGraph S).dist a a' = criticalDistance S ∧
    ¬ vertexZ S a ≤ neighborhoodKernel S a'

namespace CriticalDistanceBasic

/-- The five conclusions of Stellmacher (1986), (1.3). -/
public structure Conclusion (S : Subgroup M) (a b : Vertex S) : Prop where
  twoCore_sylow_kernel :
    IsSylowSubgroupIn (vertexTwoCore S a) (neighborhoodKernel S a)
  edgeCore_le_neighbor_stabilizer :
    edgeTwoCore S a b ≤ stabilizer S b
  edgeCore_normal_neighbor :
    ((edgeTwoCore S a b).subgroupOf (stabilizer S b)).Normal
  edgeCore_le_neighbor_kernel :
    edgeTwoCore S a b ≤ neighborhoodKernel S b
  criticalDistance_even : Even (criticalDistance S)
  vertexZ_ne_sylowOmega :
    ∀ T : Sylow 2 (stabilizer S a), vertexZ S a ≠ sylowOmegaAt S a T
  vertexZ_le_coreOmega_or_distance_zero :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) ∨
      criticalDistance S = 0

end CriticalDistanceBasic

private def actEquiv (S : Subgroup M) (g : FreeAmalgam S) : Vertex S ≃ Vertex S where
  toFun := act S g
  invFun := act S g⁻¹
  left_inv := fun d => by rw [← act_mul]; simp
  right_inv := fun d => by rw [← act_mul]; simp

private def actIso (S : Subgroup M) (g : FreeAmalgam S) :
    cosetGraph S ≃g cosetGraph S :=
  RelIso.mk (actEquiv S g) (fun {d e} => by
    change (cosetGraph S).Adj (act S g d) (act S g e) ↔
      (cosetGraph S).Adj d e
    rw [cosetGraph_adj, cosetGraph_adj]
    exact adjacent_act_iff S g d e)

private theorem dist_act (S : Subgroup M) (g : FreeAmalgam S) (d e : Vertex S) :
    (cosetGraph S).dist (act S g d) (act S g e) =
      (cosetGraph S).dist d e := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist d e
    calc
      (cosetGraph S).dist (act S g d) (act S g e) ≤
          (p.map (actIso S g).toRelEmbedding.toRelHom).length := SimpleGraph.dist_le _
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
            (p.map (actIso S g⁻¹).toRelEmbedding.toRelHom).length := SimpleGraph.dist_le _
        _ = p.length := SimpleGraph.Walk.length_map _ _
        _ = (cosetGraph S).dist (act S g d) (act S g e) := hp
    simpa [← act_mul] using hle

private theorem neighborhoodKernel_act (S : Subgroup M)
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
        have := (adjacent_act_iff S g⁻¹ (act S g d) f).2 hf
        simpa [e, ← act_mul] using this
      have hfe : act S g e = f := by
        dsimp [e]
        rw [← act_mul]
        simp
      rw [← hfe, stabilizer_act]
      exact ⟨k, hk.2 e he, rfl⟩

private noncomputable instance finiteMulAut [Finite M] (S : Subgroup M) :
    Finite (MulAut S) := by
  apply Finite.of_injective (fun f : MulAut S ↦ (f : S → S))
  intro f g hfg
  apply DFunLike.ext f g
  intro s
  exact congrFun hfg s

private noncomputable instance finiteHolomorph [Finite M] (S : Subgroup M) :
    Finite (Holomorph S) := by
  apply Finite.of_injective (fun h : Holomorph S ↦ (h.left, h.right))
  intro x y hxy
  exact SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

private noncomputable instance finiteMbar [Finite M] (S : Subgroup M) :
    Finite (Mbar S) := by
  apply Finite.of_surjective
    (fun m : M ↦ ⟨embedM S m, ⟨m, rfl⟩⟩)
  rintro ⟨x, m, rfl⟩
  exact ⟨m, rfl⟩

private noncomputable instance finiteHbar [Finite M] (S : Subgroup M) :
    Finite (Hbar S) := by
  apply Finite.of_surjective
    (fun h : Holomorph S ↦ ⟨embedH S h, ⟨h, rfl⟩⟩)
  rintro ⟨x, h, rfl⟩
  exact ⟨h, rfl⟩

public noncomputable instance finiteStabilizer [Finite M]
    (S : Subgroup M) (d : Vertex S) : Finite (stabilizer S d) := by
  rcases stabilizer_conjugate_factor S d with ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [hx]
    exact Finite.of_equiv (Mbar S)
      (Subgroup.equivMapOfInjective (Mbar S)
        (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).toEquiv
  · rw [hx]
    exact Finite.of_equiv (Hbar S)
      (Subgroup.equivMapOfInjective (Hbar S)
        (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).toEquiv

private noncomputable def sylowOmegaJoin
    {G : Type*} [Group G] (P : Subgroup G) : Subgroup G :=
  sSup {Z : Subgroup G | ∃ T : Sylow 2 P,
    Z = omegaOneCenterAmbient ((T : Subgroup P).map P.subtype)}

private theorem sylowAmbient_map_equiv
    {G G' : Type*} [Group G] [Group G'] (f : G ≃* G')
    (P : Subgroup G) [Finite P] (T : Sylow 2 P) :
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    let T' : Sylow 2 (P.map f.toMonoidHom) :=
      T.mapSurjective hfP
    ((T' : Subgroup (P.map f.toMonoidHom)).map
        (P.map f.toMonoidHom).subtype) =
      (((T : Subgroup P).map P.subtype).map f.toMonoidHom) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  change (((T : Subgroup P).map _).map _) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem sylowOmegaJoin_map_equiv
    {G G' : Type*} [Group G] [Group G'] (f : G ≃* G')
    (P : Subgroup G) [Finite P] :
    sylowOmegaJoin (P.map f.toMonoidHom) =
      (sylowOmegaJoin P).map f.toMonoidHom := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · unfold sylowOmegaJoin
    rw [sSup_eq_iSup]
    refine iSup_le fun W ↦ ?_
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T', rfl⟩
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hfP 2 T'
    rw [← hT, sylowAmbient_map_equiv,
      omegaOneCenterAmbient_map_injective f.toMonoidHom f.injective]
    exact Subgroup.map_mono (le_sSup ⟨T, rfl⟩)
  · unfold sylowOmegaJoin
    rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun W ↦ ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T, rfl⟩
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    let T' : Sylow 2 (P.map f.toMonoidHom) :=
      T.mapSurjective hfP
    rw [← omegaOneCenterAmbient_map_injective f.toMonoidHom f.injective,
      ← sylowAmbient_map_equiv]
    exact le_sSup ⟨T', rfl⟩

private theorem vertexZ_act [Finite M] (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    vertexZ S (act S g d) =
      (vertexZ S d).map (MulAut.conj g⁻¹).toMonoidHom := by
  change sylowOmegaJoin (stabilizer S (act S g d)) =
    (sylowOmegaJoin (stabilizer S d)).map
      (MulAut.conj g⁻¹).toMonoidHom
  rw [stabilizer_act]
  exact sylowOmegaJoin_map_equiv (MulAut.conj g⁻¹) (stabilizer S d)

private theorem omegaOneCenterAmbient_le (S : Subgroup M)
    (Q : Subgroup (FreeAmalgam S)) :
    omegaOneCenterAmbient Q ≤ Q := by
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff Q x).mp hx |>.1

public theorem vertexZ_le_stabilizer (S : Subgroup M) (d : Vertex S) :
    vertexZ S d ≤ stabilizer S d := by
  apply sSup_le
  rintro Z ⟨T, rfl⟩
  exact (omegaOneCenterAmbient_le S (sylowAt S d T)).trans
    (Subgroup.map_subtype_le _)

public theorem vertexZ_normal_stabilizer [Finite M]
    (S : Subgroup M) (d : Vertex S) :
    ((vertexZ S d).subgroupOf (stabilizer S d)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (vertexZ_le_stabilizer S d)).mpr
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hxfix : act S (x : FreeAmalgam S) d = d := hx
  have hxinvfix : act S (x : FreeAmalgam S)⁻¹ d = d := by
    calc
      act S (x : FreeAmalgam S)⁻¹ d =
          act S (x : FreeAmalgam S)⁻¹
            (act S (x : FreeAmalgam S) d) := by rw [hxfix]
      _ = d := by rw [← act_mul]; simp
  have hmap : vertexZ S d =
      (vertexZ S d).map (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by
    have h := vertexZ_act S (x : FreeAmalgam S)⁻¹ d
    simpa [hxinvfix] using h
  constructor
  · intro hz
    rw [hmap]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · intro hz
    rw [hmap, Subgroup.mem_map_equiv] at hz
    simpa [MulAut.conj_apply, mul_assoc] using hz

private theorem normalizer_le_normalizer_omegaOneCenterAmbient
    {G : Type*} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (omegaOneCenterAmbient Q : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  have hQmap : Q.map (MulAut.conj g).toMonoidHom = Q := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply, mul_assoc] using hg (g⁻¹ * x * g)
  have hOmap : (omegaOneCenterAmbient Q).map
      (MulAut.conj g).toMonoidHom = omegaOneCenterAmbient Q := by
    rw [← omegaOneCenterAmbient_map_injective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hQmap]
  intro x
  constructor
  · intro hx
    rw [← hOmap]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← hOmap, Subgroup.mem_map_equiv] at hx
    simpa [MulAut.conj_apply, mul_assoc] using hx

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

/-- An M-side vertex stabilizer is isomorphic to the original group. -/
public theorem mOrbit_stabilizer_nonempty_mulEquiv (S : Subgroup M)
    (a : Vertex S) (ha : InMVertexOrbit S a) :
    Nonempty (M ≃* stabilizer S a) := by
  obtain ⟨g, rfl⟩ := ha
  exact ⟨(baseMEquiv S).trans (stabilizerActEquiv S g (mVertex S 1))⟩

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

/-- An incident edge at an `M`-orbit vertex is an ambient Sylow subgroup
of that vertex stabilizer, as in the local geometry preceding (1.3). -/
public theorem incident_edgeStabilizer_isSylow [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    IsSylowSubgroupIn (stabilizer S a ⊓ stabilizer S b) (stabilizer S a) := by
  obtain ⟨Ta, hTa⟩ := edgeStabilizer_eq_sylowAt S T hTS a b ha hab
  exact ⟨Ta, hTa.symm⟩

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

private theorem isPGroup_sylowAt (S : Subgroup M) (d : Vertex S)
    (Td : Sylow 2 (stabilizer S d)) : IsPGroup 2 (sylowAt S d Td) := by
  unfold sylowAt
  exact Td.isPGroup'.map (stabilizer S d).subtype

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
    exact isPGroup_sylowAt S a Ta)

private theorem neighborhoodKernel_le_edge (S : Subgroup M)
    {a b : Vertex S} (hab : Adjacent S a b) :
    neighborhoodKernel S a ≤ stabilizer S a ⊓ stabilizer S b := by
  intro x hx
  exact ⟨hx.1, hx.2 b hab⟩

private theorem sylowSubgroupIn_eq_self_of_isPGroup
    {G : Type*} [Group G] (Q K : Subgroup G)
    (hKp : IsPGroup 2 K) (hQ : IsSylowSubgroupIn Q K) : Q = K := by
  obtain ⟨P, hPmap⟩ := hQ
  have htopP : IsPGroup 2 (⊤ : Subgroup K) := hKp.to_subgroup ⊤
  have htop : (⊤ : Subgroup K) = (P : Subgroup K) :=
    P.is_maximal' htopP le_top
  rw [← hPmap, ← htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem neighborhoodKernel_eq_vertexTwoCore [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    neighborhoodKernel S a = vertexTwoCore S a := by
  obtain ⟨Ta, hEdge⟩ := edgeStabilizer_eq_sylowAt S T hTS a b ha hab
  have hKEdge := neighborhoodKernel_le_edge S hab
  have hEdgeP : IsPGroup 2
      (stabilizer S a ⊓ stabilizer S b : Subgroup (FreeAmalgam S)) := by
    rw [hEdge]
    exact isPGroup_sylowAt S a Ta
  have hKP : IsPGroup 2 (neighborhoodKernel S a) :=
    (hEdgeP.to_subgroup
      ((neighborhoodKernel S a).subgroupOf
        (stabilizer S a ⊓ stabilizer S b))).of_equiv
      (Subgroup.subgroupOfEquivOfLe hKEdge)
  have hQ := (localKernel_at_mEdge S T hTS a b ha hab).1
  exact (sylowSubgroupIn_eq_self_of_isPGroup _ _ hKP hQ).symm

private theorem omegaOneCenterAmbient_ne_bot_of_isPGroup
    {G : Type*} [Group G] (P : Subgroup G) [Finite P]
    (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) :
    omegaOneCenterAmbient P ≠ ⊥ := by
  let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  let _ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center P) :=
    hP.to_subgroup (Subgroup.center P)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (Subgroup.center P) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := P) (Subgroup.center P) 2 htwo
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
  simpa [omegaOneCenterAmbient] using hbot

private theorem vertexZ_base_ne_bot [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hSne : S ≠ ⊥) : vertexZ S (mVertex S 1) ≠ ⊥ := by
  classical
  let Tb : Sylow 2 (stabilizer S (mVertex S 1)) := baseSylow S T
  have hTb : (Tb : Subgroup (stabilizer S (mVertex S 1))) =
      (T : Subgroup M).map (baseMHom S) :=
    Sylow.coe_mapSurjective (baseMHom_surjective S) T
  have hTne : (T : Subgroup M) ≠ ⊥ := by simpa [hTS] using hSne
  have hTbne : (Tb : Subgroup (stabilizer S (mVertex S 1))) ≠ ⊥ := by
    rw [hTb]
    intro hbot
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective _
      (baseMHom_injective S)).mp hbot)
  have hsylowNe : sylowAt S (mVertex S 1) Tb ≠ ⊥ := by
    unfold sylowAt
    intro hbot
    exact hTbne ((Subgroup.map_eq_bot_iff_of_injective _
      (stabilizer S (mVertex S 1)).subtype_injective).mp hbot)
  have hsylowP : IsPGroup 2 (sylowAt S (mVertex S 1) Tb) := by
    unfold sylowAt
    exact Tb.isPGroup'.map (stabilizer S (mVertex S 1)).subtype
  let eTb : Tb ≃* sylowAt S (mVertex S 1) Tb :=
    Subgroup.equivMapOfInjective (Tb : Subgroup (stabilizer S (mVertex S 1)))
      (stabilizer S (mVertex S 1)).subtype
      (stabilizer S (mVertex S 1)).subtype_injective
  let _ : Finite (sylowAt S (mVertex S 1) Tb) :=
    Finite.of_equiv Tb eTb.toEquiv
  have homegaNe : sylowOmegaAt S (mVertex S 1) Tb ≠ ⊥ :=
    omegaOneCenterAmbient_ne_bot_of_isPGroup
      (sylowAt S (mVertex S 1) Tb) hsylowP hsylowNe
  intro hZbot
  apply homegaNe
  apply le_bot_iff.mp
  rw [← hZbot]
  exact le_sSup ⟨Tb, rfl⟩

private theorem criticalDistanceSet_nonempty [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) : (criticalDistanceSet S).Nonempty := by
  classical
  have hZne := vertexZ_base_ne_bot S T hTS hSne
  have hfaith := actionKernel_eq_bot S T hTS hP
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hmoved : ∃ d : Vertex S, act S (z : FreeAmalgam S) d ≠ d := by
    by_contra hfix
    push Not at hfix
    have hzker : (z : FreeAmalgam S) ∈ actionKernel S := hfix
    have hzone : (z : FreeAmalgam S) = 1 := by
      rw [hfaith] at hzker
      simpa using hzker
    exact hz (Subtype.ext hzone)
  obtain ⟨d, hzd⟩ := hmoved
  refine ⟨(cosetGraph S).dist (mVertex S 1) d, d, rfl, ?_⟩
  intro hZkernel
  exact hzd (hZkernel z.property).1

private theorem criticalDistance_mem [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) :
    criticalDistance S ∈ criticalDistanceSet S := by
  exact Nat.sInf_mem (criticalDistanceSet_nonempty S T hTS hP hSne)

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
  · rw [← dist_act S g, hd]
  · intro hle
    have hmap : (vertexZ S (mVertex S 1)).map
          (MulAut.conj g⁻¹).toMonoidHom ≤
        (neighborhoodKernel S d₀).map
          (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hle
    rw [← vertexZ_act S g (mVertex S 1), ← neighborhoodKernel_act S g d₀,
      hd] at hmap
    exact hnot hmap

private theorem vertexZ_le_kernel_of_dist_lt [Finite M]
    (S : Subgroup M) {a d : Vertex S} (ha : InMVertexOrbit S a)
    (hlt : (cosetGraph S).dist a d < criticalDistance S) :
    vertexZ S a ≤ neighborhoodKernel S d := by
  by_contra hnot
  exact (not_le_of_gt hlt) (criticalDistance_le_of_escape S ha hnot)

/-- A center based at an M-side vertex lies in every neighborhood kernel at
strictly less than the critical distance. -/
public theorem vertexZ_le_neighborhoodKernel_of_dist_lt [Finite M]
    (S : Subgroup M) {a d : Vertex S} (ha : InMVertexOrbit S a)
    (hlt : (cosetGraph S).dist a d < criticalDistance S) :
    vertexZ S a ≤ neighborhoodKernel S d :=
  vertexZ_le_kernel_of_dist_lt S ha hlt

private theorem exists_criticalPair [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a) :
    ∃ a' : Vertex S, IsCriticalPair S a a' := by
  obtain ⟨d₀, hd₀dist, hd₀not⟩ := criticalDistance_mem S T hTS hP hSne
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g d₀, ⟨⟨g, rfl⟩, ?_, ?_⟩⟩
  · rw [dist_act]
    exact hd₀dist
  · intro hle
    change vertexZ S (act S g (mVertex S 1)) ≤
      neighborhoodKernel S (act S g d₀) at hle
    have hmap : (vertexZ S (mVertex S 1)).map
          (MulAut.conj g⁻¹).toMonoidHom ≤
        (neighborhoodKernel S d₀).map
          (MulAut.conj g⁻¹).toMonoidHom := by
      rw [vertexZ_act, neighborhoodKernel_act] at hle
      exact hle
    have horig : vertexZ S (mVertex S 1) ≤ neighborhoodKernel S d₀ := by
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hmap
    exact hd₀not horig

/-- The defining critical distance is attained from every M-side vertex. -/
public theorem criticalPair_exists [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a) :
    ∃ a' : Vertex S, IsCriticalPair S a a' :=
  exists_criticalPair S T hTS hP hSne a ha

private theorem walk_even_iff_color_eq (S : Subgroup M) {a b : Vertex S}
    (p : (cosetGraph S).Walk a b) :
    Even p.length ↔ color S a = color S b := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
      have hcolor : color S a ≠ color S b :=
        adjacent_color_ne S ((cosetGraph_adj S a b).1 hab)
      cases hca : color S a <;> cases hcb : color S b <;>
        cases hcc : color S c <;> simp_all

private theorem even_dist_iff_color_eq (S : Subgroup M) (a b : Vertex S) :
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

private theorem even_dist_m_orbit_iff (S : Subgroup M) {a : Vertex S}
    (ha : InMVertexOrbit S a) (b : Vertex S) :
    Even ((cosetGraph S).dist a b) ↔ color S b = false := by
  rw [even_dist_iff_color_eq,
    (inMVertexOrbit_iff_color_eq_false S a).1 ha]
  exact eq_comm

private theorem exists_dist_predecessor (S : Subgroup M) {a b : Vertex S}
    (hpos : 0 < (cosetGraph S).dist a b) :
    ∃ v : Vertex S, Adjacent S v b ∧
      (cosetGraph S).dist a v = (cosetGraph S).dist a b - 1 := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist a b
  have hpnon : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp]
    exact hpos
  refine ⟨p.penultimate, ?_, ?_⟩
  · exact (cosetGraph_adj S p.penultimate b).1 (p.adj_penultimate hpnon)
  · have hdrop : p.dropLast.length =
        (cosetGraph S).dist a p.penultimate :=
      SimpleGraph.length_eq_dist_of_subwalk hp
        ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
    rw [← hdrop, SimpleGraph.Walk.length_dropLast, hp]

private theorem criticalDistance_even [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) : Even (criticalDistance S) := by
  classical
  obtain ⟨a', ha'⟩ := exists_criticalPair S T hTS hP hSne
    (mVertex S 1) ⟨1, by simp⟩
  by_contra heven
  have hodd : Odd (criticalDistance S) := Nat.not_even_iff_odd.mp heven
  have hbne : criticalDistance S ≠ 0 := by
    intro hb
    rw [hb] at heven
    exact heven (by simp)
  have hbpos : 0 < criticalDistance S := Nat.pos_iff_ne_zero.mpr hbne
  obtain ⟨v, hva', hvdist⟩ := exists_dist_predecessor S (a := mVertex S 1)
    (b := a') (by simpa [ha'.2.1] using hbpos)
  have hvdist' : (cosetGraph S).dist (mVertex S 1) v =
      criticalDistance S - 1 := by
    rw [hvdist, ha'.2.1]
  have hpredEven : Even (criticalDistance S - 1) := by
    rw [Nat.even_sub (Nat.one_le_iff_ne_zero.mpr hbne)]
    exact iff_of_false heven (by simp)
  have hvOrbit : InMVertexOrbit S v := by
    rw [inMVertexOrbit_iff_color_eq_false]
    apply (even_dist_m_orbit_iff S ha'.1 v).mp
    rw [hvdist']
    exact hpredEven
  have hvlt : (cosetGraph S).dist (mVertex S 1) v < criticalDistance S := by
    rw [hvdist']
    exact Nat.sub_lt hbpos Nat.zero_lt_one
  have hZkernel : vertexZ S (mVertex S 1) ≤ neighborhoodKernel S v :=
    vertexZ_le_kernel_of_dist_lt S ha'.1 hvlt
  have hKernel : neighborhoodKernel S v = vertexTwoCore S v :=
    neighborhoodKernel_eq_vertexTwoCore S T hTS v a' hvOrbit hva'
  have hQedge : vertexTwoCore S v ≤ edgeTwoCore S v a' := by
    rw [edgeTwoCore_eq_edgeStabilizer S T hTS v a' hvOrbit hva', ← hKernel]
    exact neighborhoodKernel_le_edge S hva'
  have hEkernel : edgeTwoCore S v a' ≤ neighborhoodKernel S a' :=
    (localKernel_at_mEdge S T hTS v a' hvOrbit hva').2.2.2
  exact ha'.2.2 (hZkernel.trans (by rw [hKernel]; exact hQedge.trans hEkernel))

private theorem vertexZ_ne_bot_at_mOrbit [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a) :
    vertexZ S a ≠ ⊥ := by
  obtain ⟨g, rfl⟩ := ha
  have hbase := vertexZ_base_ne_bot S T hTS hSne
  rw [vertexZ_act]
  intro hbot
  exact hbase ((Subgroup.map_eq_bot_iff_of_injective _
    (MulAut.conj g⁻¹).injective).mp hbot)

private theorem omegaEdge_normal_neighbor [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    ((omegaOneCenterAmbient (stabilizer S a ⊓ stabilizer S b)).subgroupOf
      (stabilizer S b)).Normal := by
  have hEdgeEq := edgeTwoCore_eq_edgeStabilizer S T hTS a b ha hab
  have hEle : stabilizer S a ⊓ stabilizer S b ≤ stabilizer S b := inf_le_right
  have hEnormal :
      ((stabilizer S a ⊓ stabilizer S b).subgroupOf
        (stabilizer S b)).Normal := by
    rw [← hEdgeEq]
    exact (localKernel_at_mEdge S T hTS a b ha hab).2.2.1
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((omegaOneCenterAmbient_le S _).trans hEle)).mpr
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hEle).mp hEnormal).trans
    (normalizer_le_normalizer_omegaOneCenterAmbient _)

private theorem vertexZ_ne_sylowOmega [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a b : Vertex S)
    (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    ∀ Ta : Sylow 2 (stabilizer S a), vertexZ S a ≠ sylowOmegaAt S a Ta := by
  classical
  intro Ta hZTa
  obtain ⟨Te, hEdge⟩ := edgeStabilizer_eq_sylowAt S T hTS a b ha hab
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (stabilizer S a) Ta Te
  have hxfix : act S (x : FreeAmalgam S) a = a := x.property
  have hxinvfix : act S (x : FreeAmalgam S)⁻¹ a = a := by
    calc
      act S (x : FreeAmalgam S)⁻¹ a =
          act S (x : FreeAmalgam S)⁻¹
            (act S (x : FreeAmalgam S) a) := by rw [hxfix]
      _ = a := by rw [← act_mul]; simp
  have hZmap : vertexZ S a = (vertexZ S a).map
      (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by
    have h := vertexZ_act S (x : FreeAmalgam S)⁻¹ a
    simpa [hxinvfix] using h
  have hOmegaMap : sylowOmegaAt S a Te =
      (sylowOmegaAt S a Ta).map
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by
    rw [← hx]
    unfold sylowOmegaAt
    rw [sylowAt_smul,
      omegaOneCenterAmbient_map_injective
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom
        (MulAut.conj (x : FreeAmalgam S)).injective]
  have hZTe : vertexZ S a = sylowOmegaAt S a Te := by
    calc
      vertexZ S a = (vertexZ S a).map
          (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := hZmap
      _ = (sylowOmegaAt S a Ta).map
          (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by rw [hZTa]
      _ = sylowOmegaAt S a Te := hOmegaMap.symm
  have hZE : vertexZ S a =
      omegaOneCenterAmbient (stabilizer S a ⊓ stabilizer S b) := by
    rw [hEdge]
    exact hZTe
  have hZle : vertexZ S a ≤ stabilizer S a ⊓ stabilizer S b := by
    refine le_inf (vertexZ_le_stabilizer S a) ?_
    rw [hZE]
    exact (omegaOneCenterAmbient_le S _).trans inf_le_right
  have hZnormalA : ((vertexZ S a).subgroupOf (stabilizer S a)).Normal :=
    vertexZ_normal_stabilizer S a
  have hZnormalB : ((vertexZ S a).subgroupOf (stabilizer S b)).Normal := by
    rw [hZE]
    exact omegaEdge_normal_neighbor S T hTS a b ha hab
  have hZbot := no_common_normal_at_adjacent S T hTS hP a b hab
    (vertexZ S a) hZle hZnormalA hZnormalB
  exact (vertexZ_ne_bot_at_mOrbit S T hTS hSne a ha) hZbot

private theorem vertexZ_le_coreOmega_or_distance_zero [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a b : Vertex S)
    (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) ∨
      criticalDistance S = 0 := by
  classical
  by_cases hbzero : criticalDistance S = 0
  · exact Or.inr hbzero
  left
  have hbEven : Even (criticalDistance S) :=
    criticalDistance_even S T hTS hP hSne
  have hbgt : 1 < criticalDistance S := by
    rcases hbEven with ⟨k, hk⟩
    have hbpos : 0 < criticalDistance S := Nat.pos_iff_ne_zero.mpr hbzero
    omega
  have hZkernel : vertexZ S a ≤ neighborhoodKernel S a := by
    intro z hz
    refine ⟨vertexZ_le_stabilizer S a hz, ?_⟩
    intro d had
    have hdist : (cosetGraph S).dist a d = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj S a d).2 had)
    have hZd : vertexZ S a ≤ neighborhoodKernel S d :=
      vertexZ_le_kernel_of_dist_lt S ha (by simpa [hdist] using hbgt)
    exact (hZd hz).1
  have hKernel : neighborhoodKernel S a = vertexTwoCore S a :=
    neighborhoodKernel_eq_vertexTwoCore S T hTS a b ha hab
  have hZQ : vertexZ S a ≤ vertexTwoCore S a := by
    rw [← hKernel]
    exact hZkernel
  apply sSup_le
  rintro A ⟨Ta, rfl⟩
  intro x hx
  have hxData := (mem_omegaOneCenterAmbient_iff (sylowAt S a Ta) x).mp hx
  have hAleZ : sylowOmegaAt S a Ta ≤ vertexZ S a := by
    apply le_sSup
    exact ⟨Ta, rfl⟩
  have hAQ : x ∈ vertexTwoCore S a :=
    hZQ (hAleZ hx)
  have hQTa : vertexTwoCore S a ≤ sylowAt S a Ta := by
    unfold vertexTwoCore twoCoreAmbient sylowAt
    exact Subgroup.map_mono
      ((pCore_isPGroup (G := stabilizer S a) (p := 2)).le_sylow_of_normal Ta)
  exact (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) x).mpr
    ⟨hAQ, hxData.2.1, fun q hq ↦ hxData.2.2 q (hQTa hq)⟩

/-- Stellmacher, *Pushing up* (1986), Lemma (1.3). -/
public theorem criticalDistance_basic [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    CriticalDistanceBasic.Conclusion S a b := by
  classical
  obtain ⟨hQsyl, hEle, hEnormal, hEker⟩ :=
    localKernel_at_mEdge S T hTS a b ha hab
  exact {
    twoCore_sylow_kernel := hQsyl
    edgeCore_le_neighbor_stabilizer := hEle
    edgeCore_normal_neighbor := hEnormal
    edgeCore_le_neighbor_kernel := hEker
    criticalDistance_even := criticalDistance_even S T hTS hP hSne
    vertexZ_ne_sylowOmega := vertexZ_ne_sylowOmega S T hTS hP hSne a b ha hab
    vertexZ_le_coreOmega_or_distance_zero :=
      vertexZ_le_coreOmega_or_distance_zero S T hTS hP hSne a b ha hab }

/-- The amalgam action preserves graph distance. -/
public theorem cosetGraph_dist_act (S : Subgroup M) (g : FreeAmalgam S)
    (d e : Vertex S) :
    (cosetGraph S).dist (act S g d) (act S g e) =
      (cosetGraph S).dist d e :=
  dist_act S g d e

/-- Vertex Sylow-center groups transport by the right-action conjugation. -/
public theorem vertexZ_act_eq_map [Finite M] (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    vertexZ S (act S g d) =
      (vertexZ S d).map (MulAut.conj g⁻¹).toMonoidHom :=
  vertexZ_act S g d

/-- At an M-side vertex, the pointwise neighborhood kernel is its 2-core. -/
public theorem mVertex_neighborhoodKernel_eq_twoCore [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    neighborhoodKernel S a = vertexTwoCore S a :=
  neighborhoodKernel_eq_vertexTwoCore S T hTS a b ha hab

end Stellmacher.PushingUp
