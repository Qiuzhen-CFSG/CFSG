module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCriticalGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreOrbit
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNeighborOrbits

/-!
# Critical-pair placement on the marked Suzuki nine-path

At both marked endpoints the opposite vertex core is transitive on the
remaining neighbors. Three successive local/core transporters therefore
map any nonbacktracking three-path to any other with the same root.

The initial critical pair along the first three edges and `b > 2` force
`b = 3`. Transporting that same pair places the other three critical pairs
used by the nine-path oddness and opposite six-path regularity arguments.
No additional critical-pair, distance-three or path-transitivity premise is
introduced. With the earlier `b = 3` and center inclusion, global
critical-pair existence also supplies that initial seed: a critical first
vertex of Suzuki type would contradict minimality along its first edge.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1)(c,e), (12.7)--(12.8), printed pp.178,184--186.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem mixed_base_core_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (j : Bool) {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) x)
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) y)
    (hxn : x ≠ base (reducedFamily L S) (!j))
    (hyn : y ≠ base (reducedFamily L S) (!j)) :
    ∃ t ∈ Q (reducedFamily L S) (base (reducedFamily L S) (!j)), t • x = y := by
  let F := reducedFamily L S
  by_cases hj : j = i
  · subst j
    obtain ⟨g,hg,hgxy⟩ := linear_common_sylow_transitive h i eLin T hT hx hy hxn hyn
    have hadj : (graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
    have hnQ : Q F (base F (!i)) ≤ normalizer (Q F (base F i) : Set (G₀ L S)) :=
      ((source_Z_Q_U (reduced_triple h) _).2.trans
        ((ballKernel_one_le_edge F hadj.symm).trans inf_le_right)).trans
          (stabilizer_normalizes_Q F _)
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hnQ] at hg
    obtain ⟨c,hc,t,ht,rfl⟩ := hg
    have htx : t • x = x :=
      ((source_Z_Q_U (reduced_triple h) _).2.trans
        ((ballKernel_one_le_edge F hx).trans inf_le_right)) ht
    exact ⟨c,hc,by simpa only [mul_smul,htx] using hgxy⟩
  · have hj' : j = !i := Bool.eq_not_iff.mpr hj
    subst j
    exact suzuki_neighbor_core_transitive h (!i) hn eSuz R
      (by simpa only [Bool.not_not] using hR) hx hy hxn hyn

private theorem mixed_core_transitive_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {u v x y : Vertex (reducedFamily L S)}
    (hv : (graph (reducedFamily L S)).Adj u v)
    (hx : (graph (reducedFamily L S)).Adj u x)
    (hy : (graph (reducedFamily L S)).Adj u y) (hxv : x ≠ v) (hyv : y ≠ v) :
    ∃ g ∈ Q (reducedFamily L S) v, g • x = y := by
  let F := reducedFamily L S
  obtain ⟨s,hsu,hsv⟩ := incident_common_translate F hv.2
  have ht : v.type = !u.type := Bool.eq_not_iff.mpr hv.1.symm
  rw [ht] at hsv
  have hsu' : s⁻¹ • u = base F u.type := by
    calc
      s⁻¹ • u = s⁻¹ • (s • base F u.type) := congrArg (s⁻¹ • ·) hsu.symm
      _ = base F u.type := inv_smul_smul _ _
  have hsv' : s⁻¹ • v = base F (!u.type) := by rw [←hsv,inv_smul_smul]
  have hadj {z : Vertex F} (hz : (graph F).Adj u z) :
      (graph F).Adj (base F u.type) (s⁻¹ • z) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F s⁻¹).map_adj_iff.mpr hz
    change (graph F).Adj (s⁻¹ • u) (s⁻¹ • z) at hh
    rwa [hsu'] at hh
  have hne {z : Vertex F} (hz : z ≠ v) : s⁻¹ • z ≠ base F (!u.type) := by
    rw [←hsv']
    exact fun he => hz ((MulAction.injective s⁻¹) he)
  obtain ⟨g,hg,he⟩ := mixed_base_core_transitive h i hn eLin eSuz T hT R hR u.type
    (hadj hx) (hadj hy) (hne hxv) (hne hyv)
  refine ⟨s*g*s⁻¹,?_,?_⟩
  · have hh := mem_map_of_mem (MulAut.conj s).toMonoidHom hg
    rw [←Q_translate F,hsv] at hh
    exact hh
  · rw [mul_smul,mul_smul,he,smul_inv_smul]

/-- Actual marked linear/Suzuki core orbits give three-path transitivity
at each base vertex, with one transporter for every vertex in the path. -/
theorem source_mixed_three_path_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (j : Bool) : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S)
      (base (reducedFamily L S) j) 3 := by
  let F := reducedFamily L S
  let beta := base F j
  intro p q hp hq
  rcases p with ⟨⟨u,hu⟩,⟨⟨v,hv⟩,⟨⟨x,hx⟩,PUnit.unit⟩⟩⟩
  rcases q with ⟨⟨u',hu'⟩,⟨⟨v',hv'⟩,⟨⟨x',hx'⟩,PUnit.unit⟩⟩⟩
  have huv : (graph F).Adj beta u := hu
  have huv' : (graph F).Adj beta u' := hu'
  have huv2 : (graph F).Adj u v := hv
  have huv2' : (graph F).Adj u' v' := hv'
  have hvx : (graph F).Adj v x := hx
  have hvx' : (graph F).Adj v' x' := hx'
  have hne2 : v ≠ beta := hp.1
  have hne2' : v' ≠ beta := hq.1
  have hne2u : x ≠ u := hp.2.1
  have hne2u' : x' ≠ u' := hq.2.1
  obtain ⟨g,hg,hgu⟩ := star_locally_transitive h j huv huv'
  have hgb : g • beta = beta := star_le_stabilizer j hg
  have hgv' : (graph F).Adj u' (g • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr huv2
    change (graph F).Adj (g • u) (g • v) at hh
    rwa [hgu] at hh
  have hgne : g • v ≠ beta := fun he =>
    hne2 (MulAction.injective g (he.trans hgb.symm))
  obtain ⟨k,hk,hkv⟩ := mixed_core_transitive_at h i hn eLin eSuz T hT R hR
    huv'.symm hgv' huv2' hgne hne2'
  have hku : k • u' = u' := ((source_Z_Q_U (reduced_triple h) beta).2.trans
    ((ballKernel_one_le_edge F huv').trans inf_le_right)) hk
  have hkb : k • beta = beta := Q_le_stabilizer F beta hk
  have hkvx : (graph F).Adj v' ((k*g) • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F (k*g)).map_adj_iff.mpr hvx
    change (graph F).Adj ((k*g) • v) ((k*g) • x) at hh
    simpa only [mul_smul,hkv] using hh
  have hkn : (k*g) • x ≠ u' := fun he => hne2u (by
    apply MulAction.injective (k*g)
    calc
      (k*g) • x = u' := he
      _ = (k*g) • u := by simp only [mul_smul,hgu,hku])
  obtain ⟨t,ht,htx⟩ := mixed_core_transitive_at h i hn eLin eSuz T hT R hR
    huv2'.symm hkvx hvx' hkn hne2u'
  have htfix : t • beta = beta :=
    ((source_Z_Q_U (reduced_triple h) u').2.trans
      ((ballKernel_one_le_edge F huv'.symm).trans inf_le_right)) ht
  have htfix_u' : t • u' = u' := Q_le_stabilizer F u' ht
  have htfix_v' : t • v' = v' :=
    ((source_Z_Q_U (reduced_triple h) u').2.trans
      ((ballKernel_one_le_edge F huv2').trans inf_le_right)) ht
  refine ⟨t*(k*g),?_,?_⟩
  · rw [mul_smul,mul_smul,hgb,hkb,htfix]
  · change [beta,u,v,x].map (fun z => (t*(k*g)) • z) = [beta,u',v',x']
    simp only [List.map_cons,List.map_nil,mul_smul,hgb,hgu,
      hkb,hku,hkv,htfix,htfix_u',htfix_v']
    have hlast : t • k • g • x = x' := by
      rw [←mul_smul k g]
      exact htx
    simp only [hlast]

/-- The initial critical pair on the first three edges forces distance three. -/
theorem source_nine_path_critical_distance
    (i : Bool) (hb : 2 < b (reducedFamily L S))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hc : IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i))) :
    b (reducedFamily L S) = 3 := by
  let F := reducedFamily L S
  let q := p.take 3 (by decide)
  have hd := (graph F).dist_le q.toWalk
  rw [BasedWalk.length_toWalk] at hd
  change (graph F).dist v₀ (p.2.2.1 : Vertex F) ≤ 3 at hd
  rw [hy,hc.1] at hd
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Derive the three further critical-pair placements needed by the literal
nine-path and opposite six-path consumers from their existing initial seed. -/
theorem source_mixed_nine_path_critical_pairs
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hc : IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i))) :
    IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) (!i)) ∧
    IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) ∧
    IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb3 := source_nine_path_critical_distance i hb p hy hc
  let v3 : Vertex F := p.2.2.1
  let v4 : Vertex F := p.2.2.2.1
  let v5 : Vertex F := p.2.2.2.2.1
  let v6 : Vertex F := p.2.2.2.2.2.1
  let v7 : Vertex F := p.2.2.2.2.2.2.1
  let v8 : Vertex F := p.2.2.2.2.2.2.2.1
  have h34 : (graph F).Adj v3 v4 := p.2.2.2.1.property
  have h45 : (graph F).Adj v4 v5 := p.2.2.2.2.1.property
  have h56 : (graph F).Adj v5 v6 := p.2.2.2.2.2.1.property
  have h67 : (graph F).Adj v6 v7 := p.2.2.2.2.2.2.1.property
  have h78 : (graph F).Adj v7 v8 := p.2.2.2.2.2.2.2.1.property
  have two {a b c : Vertex F} (hab : (graph F).Adj a b) (hbc : (graph F).Adj b c) :
      a.type = c.type :=
    (Bool.eq_not_iff.mpr hab.1).trans (Bool.eq_not_iff.mpr hbc.1.symm).symm
  have h02 : v₀.type = (p.2.1 : Vertex F).type := two p.1.property p.2.1.property
  have h04 : v₀.type = v4.type := h02.trans (two p.2.2.1.property h34)
  have h06 : v₀.type = v6.type := h04.trans (two h45 h56)
  have h08 : v₀.type = v8.type := h06.trans (two h67 h78)
  let q6 : BasedWalk (graph F) 3 v6 :=
    ⟨⟨v5,h56.symm⟩,⟨⟨v4,h45.symm⟩,⟨⟨v3,h34.symm⟩,PUnit.unit⟩⟩⟩
  let q2 : BasedWalk (graph F) 3 (p.2.1 : Vertex F) :=
    ⟨p.2.2.1,⟨p.2.2.2.1,⟨p.2.2.2.2.1,PUnit.unit⟩⟩⟩
  let q8 : BasedWalk (graph F) 3 v8 :=
    ⟨⟨v7,h78.symm⟩,⟨⟨v6,h67.symm⟩,⟨⟨v5,h56.symm⟩,PUnit.unit⟩⟩⟩
  have ht := source_mixed_three_path_transitive h i hn eLin eSuz T hT R hR
  have hc6 : IsCriticalPair F v6 v3 := source_critical_pair_on_three_path (F := F)
    (reduced_triple h).generate hc hb3 q6
    ⟨hp.2.2.2.2.1.symm,hp.2.2.2.1.symm,trivial⟩ (ht _) h06.symm
  have hc2 : IsCriticalPair F (p.2.1 : Vertex F) v5 :=
    source_critical_pair_on_three_path (F := F) (reduced_triple h).generate hc hb3 q2
      ⟨hp.2.2.1,hp.2.2.2.1,trivial⟩ (ht _) h02.symm
  have hc8 : IsCriticalPair F v8 v5 := source_critical_pair_on_three_path (F := F)
    (reduced_triple h).generate hc hb3 q8
    ⟨hp.2.2.2.2.2.2.1.symm,hp.2.2.2.2.2.1.symm,trivial⟩
    (ht _) h08.symm
  exact ⟨by simpa only [v3,hy] using hc6,hc2,hc8⟩

/-- The center inclusion excludes a critical first vertex of Suzuki type.
A neighbor on a shortest path would put its center in the distant kernel. -/
theorem source_critical_pair_linear_type
    (h : HypothesisF11 L S) (i : Bool) (hb : b (reducedFamily L S) = 3)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    {a a' : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) a a') :
    a.type = i := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  by_contra hi
  have hat : a.type = !i := Bool.eq_not_iff.mpr hi
  obtain ⟨beta,hab,hd,_,_⟩ := critical_three_neighbor F (reduced_triple h).generate hb hc
  have hbt : beta.type = i :=
    (Bool.eq_not_iff.mpr (hat ▸ hab.1.symm)).trans (by simp)
  obtain ⟨g,hga,hgb⟩ := incident_common_translate F hab.2
  rw [hat] at hga
  rw [hbt] at hgb
  have hinc : Z F a ≤ Z F beta := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hzy
    rwa [←Z_translate F,←Z_translate F,hga,hgb] at hh
  exact hc.2 (hinc.trans (Z_le_U_of_dist_lt_b F beta a' (by rw [hd,hb]; decide)))

set_option backward.isDefEq.respectTransparency false in
/-- Global critical-pair existence and the earlier center inclusion produce
the initial critical pair on every normalized nonbacktracking nine-path. -/
theorem source_mixed_nine_path_initial_critical
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : b (reducedFamily L S) = 3)
    {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i)) :
    IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  obtain ⟨a,a',hc⟩ := reduced_criticalPair h
  have hat := source_critical_pair_linear_type h i hb hzy hc
  have h02 : v₀.type = (p.2.1 : Vertex F).type :=
    (Bool.eq_not_iff.mpr p.1.property.1).trans
      (Bool.eq_not_iff.mpr p.2.1.property.1.symm).symm
  have hroot : v₀.type = i := h02.trans (congrArg Subgroup.CosetGeometry.Vertex.type hm)
  let q := p.take 3 (by decide)
  have hq : q.Nonbacktracking := BasedWalk.nonbacktracking_take _ p hp
  have hcrit : IsCriticalPair F v₀ (p.2.2.1 : Vertex F) :=
    source_critical_pair_on_three_path (F := F) (reduced_triple h).generate hc hb q hq
      (source_mixed_three_path_transitive h i hn eLin eSuz T hT R hR v₀.type)
      (hroot.trans hat.symm)
  simpa only [hy] using hcrit

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
