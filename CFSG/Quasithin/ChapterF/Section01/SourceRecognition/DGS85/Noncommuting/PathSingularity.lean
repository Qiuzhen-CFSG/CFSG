module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusTwoControl
public import Theory.GroupAction.CubicTree.ArcRegularity

/-!
# The first singular path in the epsilon-two branch

The source parameter s is the least length of a nonregular path. In the
long-distance epsilon-two case, the critical path supplies a geodesic of
length b−2. The equal-center identity at its forward endpoint makes its
pointwise stabilizer fix one forward neighbor, while local rank-one
transitivity moves another; hence this path is nonregular. This proves the
source assertion s ≤ b−2 on the actual graph, without assuming the graph is a
tree or replacing the original vertex stabilizers by a kernel.

Source: DGS, *Groups and Graphs* (1985), (7.5)(4), pp.130--131; path
regularity is defined in (3.4), pp.73--74.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Inside a vertex stabilizer, normalizing an adjacent center is exactly
fixing the adjacent vertex. -/
theorem graph_neighbor_center_normalizer (h : LocallyRankOneTriple P B)
    {y t : Vertex (family P)} (hyt : (graph (family P)).Adj y t) :
    stabilizer (family P) y ⊓ normalizer (Z (family P) t : Set G) =
      stabilizer (family P) y ⊓ stabilizer (family P) t := by
  let := finite_endpoints h
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1,?_⟩
    change g • t = t
    by_contra hne
    have ha := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hyt
    change (graph (family P)).Adj (g • y) (g • t) at ha
    rw [show g • y = y from hg.1] at ha
    apply graph_neighbor_centers_ne h ha hyt hne
    rw [Z_translate]
    exact mem_normalizer_iff_map_conj_eq.mp hg.2
  · exact inf_le_inf_left _
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _))

/-- A vertex stabilizer sharing its center with a neighbor of `y` fixes
that neighbor whenever it also fixes `y`. -/
theorem graph_equal_centers_stabilizer_le (h : LocallyRankOneTriple P B)
    {u y t : Vertex (family P)} (hyt : (graph (family P)).Adj y t)
    (he : Z (family P) u = Z (family P) t) :
    stabilizer (family P) y ⊓ stabilizer (family P) u ≤ stabilizer (family P) t := by
  let := finite_endpoints h
  have hn : stabilizer (family P) u ≤ normalizer (Z (family P) t : Set G) := by
    rw [←he]
    exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)
  exact ((inf_le_inf_left _ hn).trans (graph_neighbor_center_normalizer h hyt).le).trans inf_le_right

/-- The local marked Sylow moves every neighbor other than its fixed neighbor.
Thus every pair of distinct neighbors has a third neighbor. -/
theorem graph_third_neighbor_of_localData (h : LocallyRankOneTriple P B)
    {y t x : Vertex (family P)} (hyt : (graph (family P)).Adj y t)
    (hyx : (graph (family P)).Adj y x) (hxt : x ≠ t)
    (c : LocalRankOneData (stabilizer (family P) y)
      (stabilizer (family P) y ⊓ stabilizer (family P) t)) :
    ∃ z, (graph (family P)).Adj y z ∧ z ≠ x ∧ z ≠ t := by
  classical
  let := finite_endpoints h
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let R := c.sylow
  have hRt : ∀ r ∈ (R : Subgroup c.Pstar), (r : G) • t = t := by
    intro r hr
    have hm : r ∈ normalizer (R : Set c.Pstar) := (R : Subgroup c.Pstar).le_normalizer hr
    rw [←source_star_borel c] at hm
    exact hm.2
  have hm : ∃ r ∈ (R : Subgroup c.Pstar), (r : G) • x ≠ x := by
    by_contra hn
    push Not at hn
    obtain ⟨g,hg,hgx⟩ := locally_transitive (family P) hyt hyx
    obtain ⟨l,hl,k,hk,hg'⟩ := local_star_factor c g hg
    have hlx : l • t = x := by simpa only [hg',mul_smul,show k • t = t from hk.2] using hgx
    let a : c.Pstar := ⟨l,hl⟩
    let S := R.mapSurjective (f := (MulAut.conj a⁻¹).toMonoidHom) (MulAut.conj a⁻¹).surjective
    have hSN : (S : Subgroup c.Pstar) ≤ normalizer (R : Set c.Pstar) := by
      rw [←source_star_borel c]
      rintro s ⟨r,hr,rfl⟩
      refine ⟨c.Pstar_le (SetLike.coe_mem _),?_⟩
      change (l⁻¹ * (r : G) * l⁻¹⁻¹) • t = t
      rw [inv_inv,mul_smul,mul_smul,hlx,hn r hr,←hlx,inv_smul_smul]
    have hSR : (S : Subgroup c.Pstar) ≤ R := by
      have hi := S.isPGroup'.inf_normalizer_sylow R
      rw [inf_eq_left.mpr hSN] at hi
      exact inf_eq_left.mp hi.symm
    have he : S = R := Sylow.ext (S.is_maximal' R.isPGroup' hSR).symm
    have ha : a⁻¹ ∈ normalizer (R : Set c.Pstar) := mem_normalizer_iff_map_conj_eq.mpr
      (congrArg (fun T : Sylow 2 c.Pstar => (T : Subgroup c.Pstar)) he)
    have ha' : a ∈ normalizer (R : Set c.Pstar) := by simpa using (normalizer (R : Set c.Pstar)).inv_mem ha
    rw [←source_star_borel c] at ha'
    exact hxt (hlx.symm.trans ha'.2)
  obtain ⟨r,hr,hrx⟩ := hm
  refine ⟨(r : G) • x,?_,hrx,?_⟩
  · have ha := (Subgroup.CosetGeometry.translationGraphIso (family P) (r : G)).map_adj_iff.mpr hyx
    change (graph (family P)).Adj ((r : G) • y) ((r : G) • x) at ha
    rwa [show (r : G) • y = y from c.Pstar_le r.property] at ha
  · intro he
    exact hxt ((MulAction.injective (r : G)) (he.trans (hRt r hr).symm))

/-- A path starting at an equal-center vertex cannot be regular towards the
neighbor with that center. This supplies the nonregular path in (7.5)(4). -/
theorem graph_path_not_rightRegular_of_equal_centers (h : LocallyRankOneTriple P B)
    {n : ℕ} {r u t : Vertex (family P)}
    (p : BasedWalk (graph (family P)) (n + 1) r) (hu : u ∈ p.vertices)
    (ht : Forward p t) (he : Z (family P) u = Z (family P) t)
    (c : LocalRankOneData (stabilizer (family P) p.endpoint)
      (stabilizer (family P) p.endpoint ⊓ stabilizer (family P) t)) :
    ¬ RightRegular (A := G) p := by
  obtain ⟨z,hz,hzx,hzt⟩ := graph_third_neighbor_of_localData h ht.1
    p.adj_penultimate_endpoint.symm ht.2.symm c
  intro hreg
  obtain ⟨g,hg,hgt⟩ := hreg t z ht ⟨hz,hzx⟩
  have hgy : g ∈ stabilizer (family P) p.endpoint := hg _ (by
    simpa only [BasedWalk.support_toWalk] using p.toWalk.end_mem_support)
  have hgu : g ∈ stabilizer (family P) u := hg _ hu
  have hfix : g • t = t := graph_equal_centers_stabilizer_le h ht.1 he ⟨hgy,hgu⟩
  exact hzt (hgt.symm.trans hfix)

/-- In the long-distance epsilon-two branch there is an actual nonregular
geodesic of length b-2. Thus the source minimum nonregular length is at most
b-2, as required in (7.5)(4); no tree assumption is made. -/
theorem graph_epsilonTwo_nonregular_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
 :
    b (family P) = 2 ∨ ∃ (n : ℕ) (p : BasedWalk (graph (family P)) n v),
      n + 2 = b (family P) ∧ p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  rcases graph_epsilonTwo_distance_gap h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ with hb | hb
  · exact Or.inl hb
  right
  have huw : u ≠ w := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdu
    omega
  obtain ⟨t,hwt,hut⟩ := exists_predecessor (family P) h.generate u w huw
  have hutne : u ≠ t := by
    intro he
    subst t
    simp only [SimpleGraph.dist_self] at hut
    omega
  obtain ⟨y,hty,huy⟩ := exists_predecessor (family P) h.generate u t hutne
  have hvud : (graph (family P)).dist v u = 1 := dist_eq_one_iff_adj.mpr hvu
  have htwd : (graph (family P)).dist t w = 1 := dist_eq_one_iff_adj.mpr hwt.symm
  have hytd : (graph (family P)).dist y t = 1 := dist_eq_one_iff_adj.mpr hty.symm
  have hvt : (graph (family P)).dist v t + 1 = b (family P) := by
    have h₁ := (connected_graph h).dist_triangle (u := v) (v := u) (w := t)
    have h₂ := (connected_graph h).dist_triangle (u := v) (v := t) (w := w)
    have hh := hc.1
    omega
  have hvy : (graph (family P)).dist v y = (graph (family P)).dist u y + 1 := by
    have h₁ := (connected_graph h).dist_triangle (u := v) (v := u) (w := y)
    have h₂ := (connected_graph h).dist_triangle (u := v) (v := y) (w := t)
    omega
  obtain ⟨p,_,hpy⟩ := BasedWalk.exists_geodesic ((connected_graph h) u y)
  let q : BasedWalk (graph (family P)) ((graph (family P)).dist u y + 1) v := ⟨⟨u,hvu⟩,p⟩
  have hqy : q.endpoint = y := hpy
  have hqnb : q.Nonbacktracking := BasedWalk.nonbacktracking_of_geodesic q (by rw [hqy,hvy])
  have hqt : Forward q t := by
    refine ⟨by rw [hqy]; exact hty.symm,?_⟩
    intro he
    have hdist := (graph (family P)).dist_le
      (q.take ((graph (family P)).dist u y) (Nat.le_succ _)).toWalk
    rw [BasedWalk.length_toWalk,BasedWalk.endpoint_take_penultimate,←he] at hdist
    omega
  have hid := graph_epsilonTwo_critical_centers h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hdu hvt hepsilon hnat₀ hnat₁
  refine ⟨_,q,by omega,hqnb,?_⟩
  apply graph_path_not_rightRegular_of_equal_centers h q ?_ hqt (hid.1.symm.trans hid.2.1)
    (d q.endpoint t hqt.1)
  change u ∈ v :: p.vertices
  apply List.mem_cons_of_mem
  simpa only [BasedWalk.support_toWalk] using p.toWalk.start_mem_support

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
