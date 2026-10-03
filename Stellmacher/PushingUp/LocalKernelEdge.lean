module

public import Stellmacher.PushingUp.AmalgamGraph

/-!
# Local kernels at an M-side amalgam edge

This module proves the local calculation used in parts (a) and (b) of
Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma (1.3).  For a vertex
in the orbit of the free-amalgam `M`-vertex and an adjacent vertex, the mapped
2-core of the first stabilizer is Sylow in its pointwise neighborhood kernel.
The edge 2-core is normal in the neighboring stabilizer and lies in its
pointwise kernel.

The only group-theoretic inputs are a Sylow 2-subgroup `T` of `M` and the
identification `T = S`; condition (P), faithfulness, and critical-distance
hypotheses are deliberately absent.  At the base edge, the `M`-side kernel is
both a normal 2-subgroup and contains `O₂(M)`, so it equals the mapped
2-core.  On the holomorph side, the normal base copy `Sbar` is both the edge
2-core and the pointwise kernel.  Local transitivity proves the required
kernel containments.  Finally, an oriented edge in the `M`-vertex orbit is a
simultaneous action translate of the base edge; stabilizers, pointwise
kernels, 2-cores, Sylow data, and relative normality are transported through
the resulting conjugation by `g⁻¹`.

The three public definitions are the lowest-layer graph-local notation used
again by the critical-distance argument.  The vertex-core transport formula
is public so subsequent orbit arguments can use the same right-action
convention.  Base identifications and the remaining transport lemmas are private.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

/-- The source's orbit `delta^G`, where `delta` is the base `M`-vertex. -/
@[expose] public def InMVertexOrbit (S : Subgroup M) (a : Vertex S) : Prop :=
  ∃ g : FreeAmalgam S, a = act S g (mVertex S 1)

/-- The source's `Q_a = O₂(G_a)`, embedded in the free amalgam. -/
@[expose] public noncomputable def vertexTwoCore (S : Subgroup M)
    (a : Vertex S) : Subgroup (FreeAmalgam S) :=
  twoCoreAmbient (stabilizer S a)

/-- The 2-core of the stabilizer of an edge. -/
@[expose] public noncomputable def edgeTwoCore (S : Subgroup M)
    (a b : Vertex S) : Subgroup (FreeAmalgam S) :=
  twoCoreAmbient (stabilizer S a ⊓ stabilizer S b)

private theorem neighborhoodKernel_le_stabilizer (S : Subgroup M) (d : Vertex S) :
    neighborhoodKernel S d ≤ stabilizer S d :=
  fun _ h => h.1

private theorem neighborhoodKernel_normal (S : Subgroup M) (d : Vertex S) :
    ((neighborhoodKernel S d).subgroupOf (stabilizer S d)).Normal := by
  constructor
  intro n hn g
  change (g : FreeAmalgam S) * (n : FreeAmalgam S) * (g : FreeAmalgam S)⁻¹ ∈
    neighborhoodKernel S d
  change _ ∈ stabilizer S d ∧
    ∀ e : Vertex S, Adjacent S d e → _ ∈ stabilizer S e
  constructor
  · change act S ((g : FreeAmalgam S) * (n : FreeAmalgam S) *
        (g : FreeAmalgam S)⁻¹) d = d
    calc
      act S ((g : FreeAmalgam S) * (n : FreeAmalgam S) *
          (g : FreeAmalgam S)⁻¹) d =
          act S (g : FreeAmalgam S)⁻¹
            (act S (n : FreeAmalgam S) (act S (g : FreeAmalgam S) d)) := by
              simp only [act_mul, mul_assoc]
      _ = act S (g : FreeAmalgam S)⁻¹
            (act S (n : FreeAmalgam S) d) := by rw [g.property]
      _ = act S (g : FreeAmalgam S)⁻¹ d := by
            rw [show act S (n : FreeAmalgam S) d = d from hn.1]
      _ = d := by
        calc
          act S (g : FreeAmalgam S)⁻¹ d =
              act S (g : FreeAmalgam S)⁻¹ (act S (g : FreeAmalgam S) d) := by
                rw [g.property]
          _ = d := by rw [← act_mul]; simp
  · intro e he
    let e0 := act S (g : FreeAmalgam S) e
    have he0 : Adjacent S d e0 := by
      have hmap := (adjacent_act_iff S (g : FreeAmalgam S) d e).2 he
      rw [g.property] at hmap
      exact hmap
    have hne0 : (n : FreeAmalgam S) ∈ stabilizer S e0 := hn.2 e0 he0
    change act S ((g : FreeAmalgam S) * (n : FreeAmalgam S) *
        (g : FreeAmalgam S)⁻¹) e = e
    calc
      act S ((g : FreeAmalgam S) * (n : FreeAmalgam S) *
          (g : FreeAmalgam S)⁻¹) e =
          act S (g : FreeAmalgam S)⁻¹
            (act S (n : FreeAmalgam S) (act S (g : FreeAmalgam S) e)) := by
              simp only [act_mul, mul_assoc]
      _ = act S (g : FreeAmalgam S)⁻¹ e0 := by rw [hne0]
      _ = e := by
        dsimp [e0]
        rw [← act_mul]
        simp

private theorem normal_le_neighborhoodKernel [Finite M]
    (S : Subgroup M) {d e : Vertex S} (hde : Adjacent S d e)
    (N : Subgroup (FreeAmalgam S))
    (hNd : N ≤ stabilizer S d) (hNe : N ≤ stabilizer S e)
    (hNnormal : (N.subgroupOf (stabilizer S d)).Normal) :
    N ≤ neighborhoodKernel S d := by
  intro n hn
  refine ⟨hNd hn, ?_⟩
  intro f hdf
  obtain ⟨g, hgd, hgef⟩ := stabilizer_transitive_neighbors S d hde hdf
  let nd : stabilizer S d := ⟨n, hNd hn⟩
  let gd : stabilizer S d := ⟨g, hgd⟩
  have hnconj : g * n * g⁻¹ ∈ N := by
    exact hNnormal.conj_mem nd hn gd
  have hfix : act S (g * n * g⁻¹) e = e := hNe hnconj
  change act S n f = f
  rw [← hgef]
  calc
    act S n (act S g e) = act S (g * n) e := (act_mul S g n e).symm
    _ = act S ((g * n * g⁻¹) * g) e := by simp [mul_assoc]
    _ = act S g (act S (g * n * g⁻¹) e) := act_mul S _ g e
    _ = act S g e := congrArg (act S g) hfix

private theorem Sbar_isPGroup (S : Subgroup M) (hSp : IsPGroup 2 S) :
    IsPGroup 2 (Sbar S) := by
  have htop : IsPGroup 2 (⊤ : Subgroup S) := hSp.to_subgroup ⊤
  have hmap := htop.map (embedS S)
  rw [← MonoidHom.range_eq_map] at hmap
  exact hmap

private theorem le_twoCoreAmbient_of_normal_isPGroup
    {G : Type u} [Group G] (K H : Subgroup G)
    (hKH : K ≤ H) (hKnormal : (K.subgroupOf H).Normal)
    (hKp : IsPGroup 2 K) :
    K ≤ twoCoreAmbient H := by
  have hKintp : IsPGroup 2 (K.subgroupOf H) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm
  have hle : K.subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨hKnormal, hKintp⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

private theorem Sbar_normal_Hbar (S : Subgroup M) :
    ((Sbar S).subgroupOf (Hbar S)).Normal := by
  constructor
  intro n hn g
  change (g : FreeAmalgam S) * (n : FreeAmalgam S) *
      (g : FreeAmalgam S)⁻¹ ∈ Sbar S
  obtain ⟨h, hh⟩ := g.property
  obtain ⟨s, hs⟩ := hn
  have hnormal : (SemidirectProduct.inl : S →* Holomorph S).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hconj : h * SemidirectProduct.inl s * h⁻¹ ∈
      (SemidirectProduct.inl : S →* Holomorph S).range :=
    hnormal.conj_mem (SemidirectProduct.inl s) ⟨s, rfl⟩ h
  obtain ⟨t, ht⟩ := hconj
  refine ⟨t, ?_⟩
  have hcomp (x : S) : embedH S (SemidirectProduct.inl x) = embedS S x :=
    DFunLike.congr_fun (embedH_comp_inl S) x
  calc
    embedS S t = embedH S (SemidirectProduct.inl t) := (hcomp t).symm
    _ = embedH S (h * SemidirectProduct.inl s * h⁻¹) := congrArg (embedH S) ht
    _ = embedH S h * embedH S (SemidirectProduct.inl s) * (embedH S h)⁻¹ := by simp
    _ = (g : FreeAmalgam S) * (n : FreeAmalgam S) * (g : FreeAmalgam S)⁻¹ := by
      rw [hh, hcomp, hs]
      rfl

private def baseMHom (S : Subgroup M) :
    M →* stabilizer S (mVertex S 1) :=
  (embedM S).codRestrict _ (fun m => by
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
    ((baseSylow S T : Sylow 2 (stabilizer S (mVertex S 1))) :
        Subgroup (stabilizer S (mVertex S 1))).map
          (stabilizer S (mVertex S 1)).subtype = Sbar S := by
  unfold baseSylow
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

private theorem base_m_kernel_le_Sbar (S : Subgroup M) :
    neighborhoodKernel S (mVertex S 1) ≤ Sbar S := by
  intro x hx
  rw [← base_edge_stabilizer]
  exact ⟨hx.1, hx.2 (hVertex S 1) (base_adjacent S)⟩

private theorem base_m_twoCore_le_Sbar [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S) :
    vertexTwoCore S (mVertex S 1) ≤ Sbar S := by
  let Tb : Sylow 2 (stabilizer S (mVertex S 1)) := baseSylow S T
  have hcoreTb : pCore 2 (stabilizer S (mVertex S 1)) ≤
      (Tb : Subgroup (stabilizer S (mVertex S 1))) :=
    (pCore_isPGroup (p := 2) (G := stabilizer S (mVertex S 1))).le_sylow_of_normal Tb
  unfold vertexTwoCore twoCoreAmbient
  calc
    (pCore 2 (stabilizer S (mVertex S 1))).map
        (stabilizer S (mVertex S 1)).subtype ≤
      (Tb : Subgroup (stabilizer S (mVertex S 1))).map
        (stabilizer S (mVertex S 1)).subtype := Subgroup.map_mono hcoreTb
    _ = Sbar S := baseSylow_ambient_eq_Sbar S T hTS

private theorem base_m_twoCore_le_kernel [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S) :
    vertexTwoCore S (mVertex S 1) ≤
      neighborhoodKernel S (mVertex S 1) := by
  apply normal_le_neighborhoodKernel S (base_adjacent S)
  · exact Subgroup.map_subtype_le _
  · rw [stabilizer_h_base]
    exact (base_m_twoCore_le_Sbar S T hTS).trans (by
      rw [← Mbar_inf_Hbar]
      exact inf_le_right)
  · unfold vertexTwoCore twoCoreAmbient
    rw [subgroupOf_map_subtype_eq]
    infer_instance

private theorem base_m_kernel_le_twoCore [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S) :
    neighborhoodKernel S (mVertex S 1) ≤
      vertexTwoCore S (mVertex S 1) := by
  have hKS := base_m_kernel_le_Sbar S
  have hSp : IsPGroup 2 S := by
    rw [← hTS]
    exact T.isPGroup'
  have hSbarp : IsPGroup 2 (Sbar S) := Sbar_isPGroup S hSp
  have hKp : IsPGroup 2 (neighborhoodKernel S (mVertex S 1)) :=
    (hSbarp.to_subgroup
      ((neighborhoodKernel S (mVertex S 1)).subgroupOf (Sbar S))).of_equiv
        (Subgroup.subgroupOfEquivOfLe hKS)
  exact le_twoCoreAmbient_of_normal_isPGroup
    (neighborhoodKernel S (mVertex S 1))
    (stabilizer S (mVertex S 1))
    (neighborhoodKernel_le_stabilizer S (mVertex S 1))
    (neighborhoodKernel_normal S (mVertex S 1)) hKp

private theorem base_m_kernel_eq_twoCore [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S) :
    neighborhoodKernel S (mVertex S 1) =
      vertexTwoCore S (mVertex S 1) :=
  le_antisymm (base_m_kernel_le_twoCore S T hTS)
    (base_m_twoCore_le_kernel S T hTS)

private theorem base_h_Sbar_le_kernel [Finite M] (S : Subgroup M) :
    Sbar S ≤ neighborhoodKernel S (hVertex S 1) := by
  apply normal_le_neighborhoodKernel S (adjacent_symm S (base_adjacent S))
  · rw [stabilizer_h_base, ← Mbar_inf_Hbar]
    exact inf_le_right
  · rw [stabilizer_m_base, ← Mbar_inf_Hbar]
    exact inf_le_left
  · rw [stabilizer_h_base]
    exact Sbar_normal_Hbar S

private theorem base_h_kernel_le_Sbar (S : Subgroup M) :
    neighborhoodKernel S (hVertex S 1) ≤ Sbar S := by
  intro x hx
  rw [← base_edge_stabilizer]
  exact ⟨hx.2 (mVertex S 1) (adjacent_symm S (base_adjacent S)), hx.1⟩

private theorem base_h_kernel_eq_Sbar [Finite M] (S : Subgroup M) :
    neighborhoodKernel S (hVertex S 1) = Sbar S :=
  le_antisymm (base_h_kernel_le_Sbar S) (base_h_Sbar_le_kernel S)

private theorem twoCoreAmbient_eq_self_of_isPGroup
    {G : Type u} [Group G] (H : Subgroup G) (hHp : IsPGroup 2 H) :
    twoCoreAmbient H = H := by
  have htopP : IsPGroup 2 (⊤ : Subgroup H) := hHp.to_subgroup ⊤
  have hcoreTop : pCore 2 H = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, htopP⟩
  unfold twoCoreAmbient
  rw [hcoreTop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem base_edge_twoCore_eq_Sbar
    (S : Subgroup M) (hSp : IsPGroup 2 S) :
    edgeTwoCore S (mVertex S 1) (hVertex S 1) = Sbar S := by
  unfold edgeTwoCore
  rw [base_edge_stabilizer]
  exact twoCoreAmbient_eq_self_of_isPGroup (Sbar S) (Sbar_isPGroup S hSp)

private theorem isSylowSubgroupIn_self_of_isPGroup
    {G : Type u} [Group G] (H : Subgroup G) (hHp : IsPGroup 2 H) :
    IsSylowSubgroupIn H H := by
  have htopP : IsPGroup 2 (⊤ : Subgroup H) := hHp.to_subgroup ⊤
  have hindex : ¬ 2 ∣ (⊤ : Subgroup H).index := by simp
  let P : Sylow 2 H := htopP.toSylow hindex
  refine ⟨P, ?_⟩
  change (⊤ : Subgroup H).map H.subtype = H
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem base_m_twoCore_isSylow_kernel [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S) :
    IsSylowSubgroupIn (vertexTwoCore S (mVertex S 1))
      (neighborhoodKernel S (mVertex S 1)) := by
  rw [base_m_kernel_eq_twoCore S T hTS]
  apply isSylowSubgroupIn_self_of_isPGroup
  unfold vertexTwoCore twoCoreAmbient
  exact (pCore_isPGroup (p := 2) (G := stabilizer S (mVertex S 1))).map
    (stabilizer S (mVertex S 1)).subtype

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

/-- The vertex two-core is transported by conjugation by `g⁻¹` under the
right action of `g` on the amalgam graph. -/
public theorem vertexTwoCore_act_eq_map
    (S : Subgroup M) (g : FreeAmalgam S) (d : Vertex S) :
    vertexTwoCore S (act S g d) =
      (vertexTwoCore S d).map (MulAut.conj g⁻¹).toMonoidHom := by
  unfold vertexTwoCore
  rw [stabilizer_act]
  exact twoCoreAmbient_map_equiv (MulAut.conj g⁻¹) (stabilizer S d)

private theorem isSylowSubgroupIn_map_equiv
    {G : Type u} [Group G]
    (e : G ≃* G) (A P : Subgroup G)
    [Finite P]
    (h : IsSylowSubgroupIn A P) :
    IsSylowSubgroupIn (A.map (e : G →* G)) (P.map (e : G →* G)) := by
  obtain ⟨T, hTmap⟩ := h
  let eP : P ≃* P.map (e : G →* G) := e.subgroupMap P
  have hePsur : Function.Surjective (eP : P →* P.map (e : G →* G)) := by
    intro y
    exact ⟨eP.symm y, eP.apply_symm_apply y⟩
  let T' : Sylow 2 (P.map (e : G →* G)) :=
    Sylow.mapSurjective hePsur T
  refine ⟨T', ?_⟩
  have hT' : (T' : Subgroup (P.map (e : G →* G))) =
      (T : Subgroup P).map (eP : P →* P.map (e : G →* G)) :=
    Sylow.coe_mapSurjective hePsur T
  rw [hT', map_internal_ambient, hTmap]

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

private theorem relativeNormal_map_equiv
    {G : Type u} [Group G] (e : G ≃* G) (A H : Subgroup G)
    (hAH : A ≤ H) (hN : (A.subgroupOf H).Normal) :
    ((A.map (e : G →* G)).subgroupOf (H.map (e : G →* G))).Normal := by
  let eH : H ≃* H.map (e : G →* G) := e.subgroupMap H
  have hmap : ((A.subgroupOf H).map (eH : H →* H.map (e : G →* G))).Normal :=
    hN.map (eH : H →* H.map (e : G →* G)) eH.surjective
  have heq : (A.subgroupOf H).map (eH : H →* H.map (e : G →* G)) =
      (A.map (e : G →* G)).subgroupOf (H.map (e : G →* G)) := by
    apply Subgroup.map_injective
      (H.map (e : G →* G)).subtype_injective
    rw [map_internal_ambient, Subgroup.map_subgroupOf_eq_of_le
      (Subgroup.map_mono hAH), Subgroup.map_subgroupOf_eq_of_le hAH]
  rw [← heq]
  exact hmap

private theorem exists_action_base_edge [Finite M]
    (S : Subgroup M) (a b : Vertex S)
    (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    ∃ g : FreeAmalgam S,
      a = act S g (mVertex S 1) ∧ b = act S g (hVertex S 1) := by
  obtain ⟨x, hax⟩ := ha
  have hae : Adjacent S a (act S x (hVertex S 1)) := by
    rw [hax]
    exact (adjacent_act_iff S x (mVertex S 1) (hVertex S 1)).2 (base_adjacent S)
  obtain ⟨y, hya, hyb⟩ := stabilizer_transitive_neighbors S a hae hab
  refine ⟨x * y, ?_, ?_⟩
  · rw [act_mul, ← hax]
    exact hya.symm
  · rw [act_mul]
    exact hyb.symm

/-- The local calculation in Stellmacher, *Pushing up* (1986), (1.3)(a),(b). -/
public theorem localKernel_at_mEdge [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a b : Vertex S) (ha : InMVertexOrbit S a) (hab : Adjacent S a b) :
    IsSylowSubgroupIn (vertexTwoCore S a) (neighborhoodKernel S a) ∧
    edgeTwoCore S a b ≤ stabilizer S b ∧
    ((edgeTwoCore S a b).subgroupOf (stabilizer S b)).Normal ∧
    edgeTwoCore S a b ≤ neighborhoodKernel S b := by
  classical
  obtain ⟨g, rfl, rfl⟩ := exists_action_base_edge S a b ha hab
  let c : FreeAmalgam S ≃* FreeAmalgam S := MulAut.conj g⁻¹
  let _ : Finite (stabilizer S (mVertex S 1)) :=
    Finite.of_equiv M (baseMEquiv S).toEquiv
  let _ : Finite (neighborhoodKernel S (mVertex S 1)) :=
    Finite.of_equiv
      ((neighborhoodKernel S (mVertex S 1)).subgroupOf
        (stabilizer S (mVertex S 1)))
      (Subgroup.subgroupOfEquivOfLe
        (neighborhoodKernel_le_stabilizer S (mVertex S 1))).toEquiv
  have hQmap : vertexTwoCore S (act S g (mVertex S 1)) =
      (vertexTwoCore S (mVertex S 1)).map (c : FreeAmalgam S →* FreeAmalgam S) := by
    unfold vertexTwoCore
    rw [stabilizer_act]
    exact twoCoreAmbient_map_equiv c _
  have hEmap : edgeTwoCore S (act S g (mVertex S 1))
      (act S g (hVertex S 1)) =
      (edgeTwoCore S (mVertex S 1) (hVertex S 1)).map
        (c : FreeAmalgam S →* FreeAmalgam S) :=
    edgeTwoCore_act S g (mVertex S 1) (hVertex S 1)
  have hMKernelMap : neighborhoodKernel S (act S g (mVertex S 1)) =
      (neighborhoodKernel S (mVertex S 1)).map
        (c : FreeAmalgam S →* FreeAmalgam S) :=
    neighborhoodKernel_act S g (mVertex S 1)
  have hHKernelMap : neighborhoodKernel S (act S g (hVertex S 1)) =
      (neighborhoodKernel S (hVertex S 1)).map
        (c : FreeAmalgam S →* FreeAmalgam S) :=
    neighborhoodKernel_act S g (hVertex S 1)
  have hHStabMap : stabilizer S (act S g (hVertex S 1)) =
      (stabilizer S (hVertex S 1)).map
        (c : FreeAmalgam S →* FreeAmalgam S) :=
    stabilizer_act S g (hVertex S 1)
  have hSp : IsPGroup 2 S := by
    rw [← hTS]
    exact T.isPGroup'
  have hEbase : edgeTwoCore S (mVertex S 1) (hVertex S 1) = Sbar S :=
    base_edge_twoCore_eq_Sbar S hSp
  have hEleH : edgeTwoCore S (mVertex S 1) (hVertex S 1) ≤
      stabilizer S (hVertex S 1) := by
    rw [hEbase, stabilizer_h_base, ← Mbar_inf_Hbar]
    exact inf_le_right
  have hEnormalH :
      ((edgeTwoCore S (mVertex S 1) (hVertex S 1)).subgroupOf
        (stabilizer S (hVertex S 1))).Normal := by
    rw [hEbase, stabilizer_h_base]
    exact Sbar_normal_Hbar S
  have hEleHKernel : edgeTwoCore S (mVertex S 1) (hVertex S 1) ≤
      neighborhoodKernel S (hVertex S 1) := by
    rw [hEbase, base_h_kernel_eq_Sbar S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQmap, hMKernelMap]
    exact isSylowSubgroupIn_map_equiv c _ _
      (base_m_twoCore_isSylow_kernel S T hTS)
  · rw [hEmap, hHStabMap]
    exact Subgroup.map_mono hEleH
  · rw [hEmap, hHStabMap]
    exact relativeNormal_map_equiv c _ _ hEleH hEnormalH
  · rw [hEmap, hHKernelMap]
    exact Subgroup.map_mono hEleHKernel

end Stellmacher.PushingUp
