module

public import Stellmacher.PushingUp.CriticalDistanceBasic

/-!
# Critical-pair endpoint geometry

This module proves the shortest-path and minimal-distance consequences used in
clauses (b)--(d) of Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma
(1.4).  For a critical pair at positive critical distance, evenness from (1.3)
places the opposite endpoint in the same M-vertex orbit.  Applying minimality
to the penultimate vertices of shortest paths gives containment of each
endpoint `vertexZ` in the opposite stabilizer.

Each `vertexZ` is normal in its own stabilizer, so the two endpoint subgroups
normalize one another and their commutator lies in their intersection.  For
the reversal statement, a hypothetical containment of the opposite
`vertexZ` in the first neighborhood kernel lets Sylow conjugacy move it into
the first vertex 2-core.  The first `vertexZ` centralizes that core by (1.3)(e),
contradicting a nontrivial endpoint commutator.  No finiteness of the vertex
set or free amalgam is used; only the finite stabilizers supplied by the
M-vertex orbit are needed.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

namespace CriticalPairPath

/-- The source-neutral endpoint geometry of a positive-distance critical pair. -/
public structure Conclusion (S : Subgroup M) (a a' : Vertex S) : Prop where
  opposite_inMVertexOrbit : InMVertexOrbit S a'
  left_Z_le_right_stabilizer : vertexZ S a ≤ stabilizer S a'
  right_Z_le_left_stabilizer : vertexZ S a' ≤ stabilizer S a
  commutator_le_intersection :
    ⁅vertexZ S a, vertexZ S a'⁆ ≤ vertexZ S a ⊓ vertexZ S a'
  reverse_critical_of_commutator_ne :
    ⁅vertexZ S a, vertexZ S a'⁆ ≠ ⊥ → IsCriticalPair S a' a

end CriticalPairPath

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

private theorem path_vertexZ_act [Finite M] (S : Subgroup M)
    (g : FreeAmalgam S) (d : Vertex S) :
    vertexZ S (act S g d) =
      (vertexZ S d).map (MulAut.conj g⁻¹).toMonoidHom := by
  change pathSylowOmegaJoin (stabilizer S (act S g d)) =
    (pathSylowOmegaJoin (stabilizer S d)).map
      (MulAut.conj g⁻¹).toMonoidHom
  rw [stabilizer_act]
  exact pathSylowOmegaJoin_map_equiv (MulAut.conj g⁻¹) (stabilizer S d)

private theorem path_criticalDistance_le_of_escape [Finite M]
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
    rw [← path_vertexZ_act S g (mVertex S 1),
      ← path_neighborhoodKernel_act S g d₀, hd] at hmap
    exact hnot hmap

private theorem path_vertexZ_le_kernel_of_dist_lt [Finite M]
    (S : Subgroup M) {a d : Vertex S} (ha : InMVertexOrbit S a)
    (hlt : (cosetGraph S).dist a d < criticalDistance S) :
    vertexZ S a ≤ neighborhoodKernel S d := by
  by_contra hnot
  exact (not_le_of_gt hlt) (path_criticalDistance_le_of_escape S ha hnot)

private theorem path_walk_even_iff_color_eq (S : Subgroup M)
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

private theorem path_even_dist_iff_color_eq (S : Subgroup M)
    (a b : Vertex S) :
    Even ((cosetGraph S).dist a b) ↔ color S a = color S b := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist a b
  rw [← hp]
  exact path_walk_even_iff_color_eq S p

private theorem path_inMVertexOrbit_iff_color_eq_false (S : Subgroup M)
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

private theorem path_even_dist_m_orbit_iff (S : Subgroup M)
    {a : Vertex S} (ha : InMVertexOrbit S a) (b : Vertex S) :
    Even ((cosetGraph S).dist a b) ↔ color S b = false := by
  rw [path_even_dist_iff_color_eq,
    (path_inMVertexOrbit_iff_color_eq_false S a).1 ha]
  exact eq_comm

private theorem path_exists_dist_predecessor (S : Subgroup M)
    {a b : Vertex S} (hpos : 0 < (cosetGraph S).dist a b) :
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

private theorem path_adjacent_of_mOrbit (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) : ∃ b : Vertex S, Adjacent S a b := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g (hVertex S 1), ?_⟩
  exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2
    (base_adjacent S)

private theorem path_vertexZ_le_endpoint_stabilizer [Finite M]
    (S : Subgroup M) {a a' : Vertex S} (ha : InMVertexOrbit S a)
    (hdist : (cosetGraph S).dist a a' = criticalDistance S) :
    vertexZ S a ≤ stabilizer S a' := by
  by_cases hbzero : criticalDistance S = 0
  · have haa' : a = a' := by
      apply (cosetGraph_connected S).dist_eq_zero_iff.mp
      rw [hdist, hbzero]
    subst a'
    exact vertexZ_le_stabilizer S a
  · have hpos : 0 < (cosetGraph S).dist a a' := by
      rw [hdist]
      exact Nat.pos_iff_ne_zero.mpr hbzero
    obtain ⟨v, hva', hvdist⟩ := path_exists_dist_predecessor S hpos
    have hvlt : (cosetGraph S).dist a v < criticalDistance S := by
      rw [hvdist, hdist]
      exact Nat.sub_lt (Nat.pos_iff_ne_zero.mpr hbzero) Nat.zero_lt_one
    have hZkernel : vertexZ S a ≤ neighborhoodKernel S v :=
      path_vertexZ_le_kernel_of_dist_lt S ha hvlt
    intro z hz
    exact (hZkernel hz).2 a' hva'

private theorem path_criticalDistance_even [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a) :
    Even (criticalDistance S) := by
  obtain ⟨b, hab⟩ := path_adjacent_of_mOrbit S a ha
  exact (criticalDistance_basic S T hTS hP hSne a b ha hab).criticalDistance_even

private theorem criticalPair_mutual_stabilizer [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a a' : Vertex S) (hcrit : IsCriticalPair S a a') :
    vertexZ S a ≤ stabilizer S a' ∧
      vertexZ S a' ≤ stabilizer S a := by
  have hbEven : Even (criticalDistance S) :=
    path_criticalDistance_even S T hTS hP hSne a hcrit.1
  have ha'Orbit : InMVertexOrbit S a' := by
    apply (path_inMVertexOrbit_iff_color_eq_false S a').2
    apply (path_even_dist_m_orbit_iff S hcrit.1 a').1
    simpa [hcrit.2.1] using hbEven
  constructor
  · exact path_vertexZ_le_endpoint_stabilizer S hcrit.1 hcrit.2.1
  · apply path_vertexZ_le_endpoint_stabilizer S ha'Orbit
    rw [SimpleGraph.dist_comm]
    exact hcrit.2.1

private theorem criticalPair_mutual_normalizer [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a a' : Vertex S) (hcrit : IsCriticalPair S a a') :
    vertexZ S a ≤ Subgroup.normalizer (vertexZ S a' : Set (FreeAmalgam S)) ∧
      vertexZ S a' ≤ Subgroup.normalizer (vertexZ S a : Set (FreeAmalgam S)) := by
  have hcont := criticalPair_mutual_stabilizer S T hTS hP hSne a a' hcrit
  have hnormA : stabilizer S a ≤
      Subgroup.normalizer (vertexZ S a : Set (FreeAmalgam S)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (vertexZ_le_stabilizer S a)).mp (vertexZ_normal_stabilizer S a)
  have hnormA' : stabilizer S a' ≤
      Subgroup.normalizer (vertexZ S a' : Set (FreeAmalgam S)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (vertexZ_le_stabilizer S a')).mp (vertexZ_normal_stabilizer S a')
  exact ⟨hcont.1.trans hnormA', hcont.2.trans hnormA⟩

private theorem path_sylowAmbient_smul
    {G : Type u} [Group G] (P : Subgroup G)
    (T : Sylow 2 P) (g : P) :
    (((g • T : Sylow 2 P) : Subgroup P).map P.subtype) =
      (((T : Subgroup P).map P.subtype).map
        (MulAut.conj (g : G)).toMonoidHom) := by
  change (((T : Subgroup P).map
      (MulAut.conj g).toMonoidHom).map P.subtype) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem path_exists_conjugate_le_sylow
    {G : Type u} [Group G] {A W P : Subgroup G} [Finite P]
    (hAP : A ≤ P) (hAp : IsPGroup 2 A)
    (hWP : IsSylowSubgroupIn W P) :
    ∃ g : P, A.map (MulAut.conj (g : G)).toMonoidHom ≤ W := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let AP : Subgroup P := A.subgroupOf P
  have hAPp : IsPGroup 2 AP :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm
  obtain ⟨U, hAU⟩ := hAPp.exists_le_sylow
  obtain ⟨T, hTmap⟩ := hWP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P U T
  refine ⟨g, ?_⟩
  have hmap :
      (((U : Subgroup P).map P.subtype).map
        (MulAut.conj (g : G)).toMonoidHom) = W := by
    rw [← path_sylowAmbient_smul, hg, hTmap]
  rw [← hmap]
  exact Subgroup.map_mono <| by
    intro x hx
    let xp : P := ⟨x, hAP hx⟩
    have hxp : xp ∈ AP := hx
    exact Subgroup.mem_map_of_mem P.subtype (hAU hxp)

private theorem path_vertexZ_le_coreOmega [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) := by
  obtain ⟨b, hab⟩ := path_adjacent_of_mOrbit S a ha
  exact (criticalDistance_basic S T hTS hP hSne a b ha hab)
    |>.vertexZ_le_coreOmega_or_distance_zero.resolve_right (Nat.ne_of_gt hb)

private theorem path_vertexZ_isPGroup [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) : IsPGroup 2 (vertexZ S a) := by
  exact (omegaOneCenterAmbient_elementaryAbelian (vertexTwoCore S a)).isPGroup.to_le
    (path_vertexZ_le_coreOmega S T hTS hP hSne a ha hb)

private theorem path_vertexZ_centralizes_core [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    ⁅vertexZ S a, vertexTwoCore S a⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hzData := (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) z).mp
    (path_vertexZ_le_coreOmega S T hTS hP hSne a ha hb hz)
  exact hzData.2.2 q hq

/-- The final reversal step of (1.4)(d), isolated from the preceding proof that
the endpoint commutator is nontrivial. -/
private theorem criticalPair_reverse_not_kernel_of_commutator_ne [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (hcomm : ⁅vertexZ S a, vertexZ S a'⁆ ≠ ⊥) :
    ¬ vertexZ S a' ≤ neighborhoodKernel S a := by
  have hbEven : Even (criticalDistance S) :=
    path_criticalDistance_even S T hTS hP hSne a hcrit.1
  have ha'Orbit : InMVertexOrbit S a' := by
    apply (path_inMVertexOrbit_iff_color_eq_false S a').2
    apply (path_even_dist_m_orbit_iff S hcrit.1 a').1
    simpa [hcrit.2.1] using hbEven
  intro hZendKernel
  obtain ⟨b, hab⟩ := path_adjacent_of_mOrbit S a hcrit.1
  have hbasicA := criticalDistance_basic S T hTS hP hSne a b hcrit.1 hab
  have hZendP : IsPGroup 2 (vertexZ S a') :=
    path_vertexZ_isPGroup S T hTS hP hSne a' ha'Orbit hb
  let _ : Finite (neighborhoodKernel S a) :=
    Finite.of_equiv
      ((neighborhoodKernel S a).subgroupOf (stabilizer S a))
      (Subgroup.subgroupOfEquivOfLe
        (show neighborhoodKernel S a ≤ stabilizer S a from
          fun _ h ↦ h.1)).toEquiv
  obtain ⟨g, hg⟩ := path_exists_conjugate_le_sylow hZendKernel hZendP
    hbasicA.twoCore_sylow_kernel
  have hgStab : (g : FreeAmalgam S) ∈ stabilizer S a := g.property.1
  have hgNorm : (g : FreeAmalgam S) ∈
      Subgroup.normalizer (vertexZ S a : Set (FreeAmalgam S)) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (vertexZ_le_stabilizer S a)).mp (vertexZ_normal_stabilizer S a)) hgStab
  have hZaMap : (vertexZ S a).map
      (MulAut.conj (g : FreeAmalgam S)).toMonoidHom = vertexZ S a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNorm
  have hmapped : (⁅vertexZ S a, vertexZ S a'⁆).map
      (MulAut.conj (g : FreeAmalgam S)).toMonoidHom = ⊥ := by
    rw [Subgroup.map_commutator, hZaMap]
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono le_rfl hg).trans
      (le_of_eq (path_vertexZ_centralizes_core S T hTS hP hSne a hcrit.1 hb))
  exact hcomm ((Subgroup.map_eq_bot_iff_of_injective
    (⁅vertexZ S a, vertexZ S a'⁆)
    (MulAut.conj (g : FreeAmalgam S)).injective).mp hmapped)

private theorem criticalPair_commutator_le_inf [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a a' : Vertex S) (hcrit : IsCriticalPair S a a') :
    ⁅vertexZ S a, vertexZ S a'⁆ ≤ vertexZ S a ⊓ vertexZ S a' := by
  have hnorm := criticalPair_mutual_normalizer S T hTS hP hSne a a' hcrit
  exact le_inf
    ((Subgroup.le_normalizer_iff_commutator_le_left).mp hnorm.2)
    ((Subgroup.le_normalizer_iff_commutator_le_right).mp hnorm.1)

private theorem criticalPair_reverse_of_commutator_ne [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (hcomm : ⁅vertexZ S a, vertexZ S a'⁆ ≠ ⊥) :
    IsCriticalPair S a' a := by
  have hbEven : Even (criticalDistance S) :=
    path_criticalDistance_even S T hTS hP hSne a hcrit.1
  have ha'Orbit : InMVertexOrbit S a' := by
    apply (path_inMVertexOrbit_iff_color_eq_false S a').2
    apply (path_even_dist_m_orbit_iff S hcrit.1 a').1
    simpa [hcrit.2.1] using hbEven
  exact ⟨ha'Orbit, by simpa [SimpleGraph.dist_comm] using hcrit.2.1,
    criticalPair_reverse_not_kernel_of_commutator_ne
      S T hTS hP hSne a a' hcrit hb hcomm⟩


/-- The endpoint-geometry part of Stellmacher, *Pushing up* (1986), Lemma
(1.4)(b)--(d). -/
public theorem criticalPair_path [Finite M]
    {S : Subgroup M}
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S) : CriticalPairPath.Conclusion S a a' := by
  have hbEven : Even (criticalDistance S) :=
    path_criticalDistance_even S T hTS hP hSne a hcrit.1
  have ha'Orbit : InMVertexOrbit S a' := by
    apply (path_inMVertexOrbit_iff_color_eq_false S a').2
    apply (path_even_dist_m_orbit_iff S hcrit.1 a').1
    simpa [hcrit.2.1] using hbEven
  have hcont := criticalPair_mutual_stabilizer S T hTS hP hSne a a' hcrit
  exact {
    opposite_inMVertexOrbit := ha'Orbit
    left_Z_le_right_stabilizer := hcont.1
    right_Z_le_left_stabilizer := hcont.2
    commutator_le_intersection :=
      criticalPair_commutator_le_inf S T hTS hP hSne a a' hcrit
    reverse_critical_of_commutator_ne :=
      criticalPair_reverse_of_commutator_ne S T hTS hP hSne a a' hcrit hb }

end Stellmacher.PushingUp
