module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCriticalPlacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiNeighborOrbits

/-!
# Three-path critical placement for the small Suzuki endpoint

The actual common Sylows and the literal Suzuki group at parameter zero
supply opposite-core transitivity at both endpoints. Successive core
transporters give three-path transitivity in the original reduced graph.
Every existing critical pair of distance three can then be placed on a
prescribed nonbacktracking three-path of the same initial type. The source
center inclusion also supplies the initial critical pair internally.

No positive Suzuki parameter, orbit callback, nine-path oddness, or Omega
identity is assumed or asserted here.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem small_mixed_base_core_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
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
    exact small_suzuki_neighbor_core_transitive h (!i) eSuz R
      (by simpa only [Bool.not_not] using hR) hx hy hxn hyn

private theorem small_mixed_core_transitive_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
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
  obtain ⟨g,hg,he⟩ := small_mixed_base_core_transitive h i eLin eSuz T hT R hR u.type
    (hadj hx) (hadj hy) (hne hxv) (hne hyv)
  refine ⟨s*g*s⁻¹,?_,?_⟩
  · have hh := mem_map_of_mem (MulAut.conj s).toMonoidHom hg
    rw [←Q_translate F,hsv] at hh
    exact hh
  · rw [mul_smul,mul_smul,he,smul_inv_smul]

/-- Actual marked linear/Suzuki core orbits give three-path transitivity
at each base vertex, with one transporter for every vertex in the path. -/
theorem small_suzuki_three_path_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
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
  obtain ⟨k,hk,hkv⟩ := small_mixed_core_transitive_at h i eLin eSuz T hT R hR
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
  obtain ⟨t,ht,htx⟩ := small_mixed_core_transitive_at h i eLin eSuz T hT R hR
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

/-- Place an actual distance-three critical pair on any prescribed three-path
of the same initial type, using the literal small Suzuki core orbits. -/
theorem small_suzuki_critical_pair_on_three_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {a a' x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a a')
    (hb : b (reducedFamily L S) = 3)
    (p : BasedWalk (graph (reducedFamily L S)) 3 x) (hp : p.Nonbacktracking)
    (hx : x.type = a.type) : IsCriticalPair (reducedFamily L S) x p.endpoint := by
  let : ∀ j, Finite (reducedFamily L S j) := finite_endpoints (reduced_triple h)
  exact source_critical_pair_on_three_path (F := reducedFamily L S)
    (reduced_triple h).generate hc hb p hp
    (small_suzuki_three_path_transitive h i eLin eSuz T hT R hR x.type) hx

/-- The source center inclusion makes every nonbacktracking three-path
starting at the linear type an actual critical pair, without a supplied seed. -/
theorem small_suzuki_linear_three_path_critical
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hb : b (reducedFamily L S) = 3)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    {x : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 3 x) (hp : p.Nonbacktracking)
    (hx : x.type = i) : IsCriticalPair (reducedFamily L S) x p.endpoint := by
  obtain ⟨a,a',hc⟩ := reduced_criticalPair h
  have hat := source_critical_pair_linear_type h i hb hzy hc
  exact small_suzuki_critical_pair_on_three_path h i eLin eSuz T hT R hR hc hb p hp
    (hx.trans hat.symm)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
