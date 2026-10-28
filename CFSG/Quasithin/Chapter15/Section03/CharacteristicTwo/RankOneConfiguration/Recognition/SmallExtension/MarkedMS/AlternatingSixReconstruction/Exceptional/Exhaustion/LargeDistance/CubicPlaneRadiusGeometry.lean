module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair

/-!
# Exact geometry of the displaced cubic radius paths

The two full radius-kernel joins constructed in `CubicPlaneRadiusPair`
fix exactly their common component endpoint z. Indeed, an actor fixing two
vertices of the actual amalgam tree fixes the path between them. At z, its
first edge stabilizer is the full two-group Q_t. A join which is not a
two-group therefore cannot fix another vertex. Its entire normalizer fixes
z as well, by conjugation covariance and uniqueness of the fixed vertex.

Each original radius kernel fixes its own critical path pointwise. Hence
the two displaced paths meet only at z. Their concatenation is a path in
the same tree, so the distance between their i-th and j-th vertices is
(4-i)+(4-j). In particular, their starts are distance eight apart, their
midpoints distance four, and their last-edge vertices distance two.
The result retains the original opposite edge and its generation identity,
both endpoint indices four, and both full midpoint and last-edge kernels.
No comparison with a separate natural-module graph is used.

The whole-core and literal C.1.32 applications keep the original cubic
projection with kernel E, both moving covers of orders sixteen and
thirty-two, and all central attachments. This establishes the geometry of
the displaced paths; it does not give the remaining terminal commutator
contradiction, other image/distance cases, or either whole-core exhaustion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the generating-stabilizer comparisons toward (5.12), printed
pp.924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem stabilizes_shortest_vertices {F : Type*} [Group F] (T : Subgroup F)
    {a b : Vertex T} (w : (cosetGraph T).Walk a b)
    (hw : w.length = (cosetGraph T).dist a b) (i : ℕ) :
    stabilizer T a ⊓ stabilizer T b ≤ stabilizer T (w.getVert i) := by
  intro g hg
  have ha : act T g a = a := hg.1
  have hb : act T g b = b := hg.2
  let w' := (actWalk T g w).copy ha hb
  have hw' : w'.length = (cosetGraph T).dist a b := by
    simpa only [w',SimpleGraph.Walk.length_copy,actWalk_length] using hw
  have he : w' = w := Subtype.mk.inj
    ((cosetGraph_isTree T).isAcyclic.subsingleton_path a b |>.elim
      ⟨w',w'.isPath_of_length_eq_dist hw'⟩ ⟨w,w.isPath_of_length_eq_dist hw⟩)
  have hv := congrArg (fun p : (cosetGraph T).Walk a b => p.getVert i) he
  change act T g (w.getVert i) = w.getVert i
  simpa only [w',SimpleGraph.Walk.getVert_copy,actWalk_getVert] using hv

private theorem edge_kernel_two {F : Type*} [Group F] [Finite F]
    (T : Subgroup F) (hT : IsPGroup 2 T) {t : Vertex T} (ht : color T t = true) :
    IsPGroup 2 (Q T t) := by
  obtain ⟨g,rfl⟩ : ∃ g, t = hVertex T g := by
    cases t with
    | inl q => cases ht
    | inr q =>
      induction q using Quotient.inductionOn
      exact ⟨_,rfl⟩
  have hh := Q_act T g (beta T)
  simp only [beta,act_hVertex,one_mul] at hh
  have hb : Q T (hVertex T 1) = T.map (embedM T) := Q_beta T
  rw [hh,hb]
  exact (hT.map (embedM T)).map _

include h in
private theorem non_two_unique_fixed_vertex
    {z : Vertex Rg} (hzcol : color Rg z = false)
    (P : Subgroup (FreeAmalgam Rg)) (hP : P ≤ stabilizer Rg z)
    (hn : ¬ IsPGroup 2 P) (v : Vertex Rg) :
    P ≤ stabilizer Rg v ↔ v = z := by
  refine ⟨fun hPv => ?_,fun he => he ▸ hP⟩
  by_contra hv
  obtain ⟨w,hw⟩ := (cosetGraph_connected Rg).exists_walk_length_eq_dist z v
  have hl : 0 < w.length := by
    by_contra! hl
    exact hv (w.eq_of_length_eq_zero (by omega)).symm
  have hadj : Adjacent Rg z (w.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (w.adj_getVert_succ (i := 0) hl)
  have ht : color Rg (w.getVert 1) = true := by
    have hc := adjacent_color_ne Rg hadj
    rw [hzcol] at hc
    cases he : color Rg (w.getVert 1) <;> simp_all
  have hQ : P ≤ Q Rg (w.getVert 1) := by
    rw [Q_h_eq_edge Rg ht hadj]
    exact le_inf hP ((le_inf hP hPv).trans (stabilizes_shortest_vertices Rg w hw 1))
  exact hn ((edge_kernel_two Rg h.relative_radical.isPGroup ht).to_le hQ)

include h in
private theorem non_two_normalizer_fixes_vertex
    {z : Vertex Rg} (hzcol : color Rg z = false)
    (P : Subgroup (FreeAmalgam Rg)) (hP : P ≤ stabilizer Rg z)
    (hn : ¬ IsPGroup 2 P) :
    normalizer (P : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z := by
  intro g hg
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (P : Set (FreeAmalgam Rg))).inv_mem hg)
  have hfix : P ≤ stabilizer Rg (act Rg g z) := by
    rw [stabilizer_act,←hPg]
    exact map_mono hP
  exact (non_two_unique_fixed_vertex h hzcol P hP hn _).mp hfix


private theorem shortest_append_at_only_common_vertex {F : Type*} [Group F] (T : Subgroup F)
    {a b z : Vertex T} (p : (cosetGraph T).Walk a z) (q : (cosetGraph T).Walk b z)
    (hp : p.IsPath) (hq : q.IsPath)
    (hcommon : ∀ v, v ∈ p.support → v ∈ q.support → v = z) :
    (p.append q.reverse).length = (cosetGraph T).dist a b := by
  have hpath : (p.append q.reverse).IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [SimpleGraph.Walk.support_append]
    apply List.nodup_append'.mpr
    refine ⟨hp.support_nodup,hq.reverse.support_nodup.tail,?_⟩
    intro v hvp hvq
    have hvq' : v ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using
        List.mem_of_mem_tail hvq
    have he := hcommon v hvp hvq'
    subst v
    have hnd := hq.reverse.support_nodup
    rw [←List.cons_head_tail q.reverse.support_ne_nil] at hnd
    have hhead : q.reverse.support.head q.reverse.support_ne_nil = z := by simp
    rw [hhead,List.nodup_cons] at hnd
    exact hnd.1 hvq
  obtain ⟨w,hw⟩ := (cosetGraph_connected T).exists_walk_length_eq_dist a b
  have he : p.append q.reverse = w := Subtype.mk.inj
    ((cosetGraph_isTree T).isAcyclic.subsingleton_path a b |>.elim
      ⟨_,hpath⟩ ⟨w,w.isPath_of_length_eq_dist hw⟩)
  exact (congrArg SimpleGraph.Walk.length he).trans hw

include h in
/-- A pair of shortest paths whose endpoint-fixing subgroups generate a
non-two-group can meet only at the shared component vertex. This determines
all cross-distances and confines the full join normalizer to that vertex. -/
theorem radius_pair_path_geometry_of_not_two
    {a b z : Vertex Rg} (hzcol : color Rg z = false)
    (p : (cosetGraph Rg).Walk a z) (q : (cosetGraph Rg).Walk b z)
    (hp : p.length = (cosetGraph Rg).dist a z)
    (hq : q.length = (cosetGraph Rg).dist b z)
    (A B : Subgroup (FreeAmalgam Rg))
    (hAa : A ≤ stabilizer Rg a) (hAz : A ≤ stabilizer Rg z)
    (hBb : B ≤ stabilizer Rg b) (hBz : B ≤ stabilizer Rg z)
    (hn : ¬ IsPGroup 2 (A ⊔ B : Subgroup (FreeAmalgam Rg))) :
    (∀ v, A ⊔ B ≤ stabilizer Rg v ↔ v = z) ∧
    normalizer ((A ⊔ B : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
    (∀ v, v ∈ p.support → v ∈ q.support → v = z) ∧
    (∀ i j, (cosetGraph Rg).dist (p.getVert i) (q.getVert j) =
      (p.length - i) + (q.length - j)) := by
  have hJ := sup_le hAz hBz
  have hfix := non_two_unique_fixed_vertex h hzcol (A ⊔ B) hJ hn
  have hcommon (v : Vertex Rg) (hvp : v ∈ p.support) (hvq : v ∈ q.support) : v = z := by
    obtain ⟨i,hi,_⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvp
    obtain ⟨j,hj,_⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvq
    apply (hfix v).mp
    apply sup_le
    · rw [←hi]
      exact (le_inf hAa hAz).trans (stabilizes_shortest_vertices Rg p hp i)
    · rw [←hj]
      exact (le_inf hBb hBz).trans (stabilizes_shortest_vertices Rg q hq j)
  refine ⟨hfix,non_two_normalizer_fixes_vertex h hzcol _ hJ hn,hcommon,?_⟩
  intro i j
  have hp' := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_drop i)
  have hq' := SimpleGraph.length_eq_dist_of_subwalk hq (q.isSubwalk_drop j)
  have he := shortest_append_at_only_common_vertex Rg (p.drop i) (q.drop j)
    ((p.drop i).isPath_of_length_eq_dist hp') ((q.drop j).isPath_of_length_eq_dist hq')
    (fun v hvp hvq => hcommon v ((p.isSubwalk_drop i).support_subset hvp)
      ((q.isSubwalk_drop j).support_subset hvq))
  simpa only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.drop_length] using he.symm

include h e hz hk in
/-- The two displaced critical paths meet only at their original common
endpoint. Both joined radius kernels determine that endpoint uniquely, and
their full normalizers fix it. Every cross-distance is the sum of the two
remaining path lengths, on the actual cubic graph. -/
theorem plane_small_four_radius_pair_geometry
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
      ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
        (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            let Y' := V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)
            let W' := V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)
            ¬ IsPGroup 2 (Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) ∧
            ¬ IsPGroup 2 (W ⊔ W' : Subgroup (FreeAmalgam Rg)) ∧
            (∀ v, (Y ⊔ Y' ≤ stabilizer Rg v ↔ v = z) ∧
              (W ⊔ W' ≤ stabilizer Rg v ↔ v = z)) ∧
            normalizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
            normalizer ((W ⊔ W' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
            (∀ v, v ∈ p.walk.support → v ∈ q.walk.support → v = z) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) := by
  obtain ⟨a,z,p,s,hzs,hgen,hiY,hiW,g,hgs,hfixz,q,hverts,hYtwo,hWtwo⟩ :=
    plane_small_four_radius_pair_not_two h e hz hk u hR hb4 hsmall
  have hbounds {b : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) b z) :
      (V Rg b ⊓ Q Rg (r.walk.getVert 2) ≤ stabilizer Rg b) ∧
      (V Rg b ⊓ Q Rg (r.walk.getVert 2) ≤ stabilizer Rg z) ∧
      (V Rg b ⊓ Q Rg (r.walk.getVert 3) ≤ stabilizer Rg b) ∧
      (V Rg b ⊓ Q Rg (r.walk.getVert 3) ≤ stabilizer Rg z) := by
    have hl : r.walk.length = 4 := r.length_eq_b.trans hb4
    have hV : V Rg b ≤ stabilizer Rg b :=
      ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) b r.start_color).trans
        (fun _ hx => hx.1)
    have hc : color Rg (r.walk.getVert 2) = false :=
      (r.vertex_color (by omega)).mpr (by decide)
    have hcz : (cosetGraph Rg).dist (r.walk.getVert 2) z = 2 := by
      rw [r.dist_end,hl]
    have htz : Adjacent Rg (r.walk.getVert 3) z := by
      have hh := r.walk.adj_getVert_succ (i := 3) (by omega)
      rw [show 3+1=r.walk.length by omega,r.walk.getVert_length] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    exact ⟨inf_le_left.trans hV,
      inf_le_right.trans (Q_le_stabilizer_of_dist_two Rg _ _ hc hcz),
      inf_le_left.trans hV,inf_le_right.trans (fun _ hx => hx.2 _ htz)⟩
  obtain ⟨hYa,hYz,hWa,hWz⟩ := hbounds p
  obtain ⟨hYb,hY'z,hWb,hW'z⟩ := hbounds q
  obtain ⟨hfixY,hNY,hcommon,hdist⟩ := radius_pair_path_geometry_of_not_two h p.end_color
    p.walk q.walk p.shortest q.shortest _ _ hYa hYz hYb hY'z hYtwo
  have hWfix := non_two_unique_fixed_vertex h p.end_color _ (sup_le hWz hW'z) hWtwo
  have hNW := non_two_normalizer_fixes_vertex h p.end_color _ (sup_le hWz hW'z) hWtwo
  refine ⟨a,z,p,s,hzs,hgen,hiY,hiW,g,hgs,hfixz,q,hverts,
    hYtwo,hWtwo,fun v => ⟨hfixY v,hWfix v⟩,hNY,hNW,hcommon,?_⟩
  have hp4 : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hq4 : q.walk.length = 4 := q.length_eq_b.trans hb4
  simpa only [hp4,hq4] using hdist


omit hk in
include h e hz in
/-- Whole-core application of the exact separation and endpoint rigidity of
both displaced radius kernels. The original cubic projection, both covers,
the Borel branch, and the remaining distance and image premises are retained. -/
theorem coreExhaustion_or_cubic_plane_radius_geometry :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
              ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                  (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                  let Y' := V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)
                  let W' := V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)
                  ¬ IsPGroup 2 (Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) ∧
                  ¬ IsPGroup 2 (W ⊔ W' : Subgroup (FreeAmalgam Rg)) ∧
                  (∀ v, (Y ⊔ Y' ≤ stabilizer Rg v ↔ v = z) ∧
                    (W ⊔ W' ≤ stabilizer Rg v ↔ v = z)) ∧
                  normalizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
                  normalizer ((W ⊔ W' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
                  (∀ v, v ∈ p.walk.support → v ∈ q.walk.support → v = z) ∧
                  (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                    (4-i) + (4-j)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_radius_pair_geometry h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the displaced-path geometry. The terminal
commutator contradiction and the other reconstruction branches remain explicit. -/
theorem rankTwo_or_cubic_plane_radius_geometry :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
              ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                  (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                  let Y' := V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)
                  let W' := V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)
                  ¬ IsPGroup 2 (Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) ∧
                  ¬ IsPGroup 2 (W ⊔ W' : Subgroup (FreeAmalgam Rg)) ∧
                  (∀ v, (Y ⊔ Y' ≤ stabilizer Rg v ↔ v = z) ∧
                    (W ⊔ W' ≤ stabilizer Rg v ↔ v = z)) ∧
                  normalizer ((Y ⊔ Y' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
                  normalizer ((W ⊔ W' : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤ stabilizer Rg z ∧
                  (∀ v, v ∈ p.walk.support → v ∈ q.walk.support → v = z) ∧
                  (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                    (4-i) + (4-j)))) :=
  (coreExhaustion_or_cubic_plane_radius_geometry h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
