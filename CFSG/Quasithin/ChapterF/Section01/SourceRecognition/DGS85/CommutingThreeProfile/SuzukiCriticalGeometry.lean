module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FullCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity

/-!
# Three-path transport for the normalized Suzuki nine-path

The adjacent-core product gives a literal transporter for every pair of
nonbacktracking three-paths with a fixed linear root.  The transporter fixes
the root, the first edge and the middle Suzuki vertex in the required order;
this is the source-exact bridge used to place all four critical pairs in the
normalized nine-path.  The critical-pair statement is kept separate from the
later commutator and regularity hypotheses.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupAction.CubicTree
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Full adjacent-core and local-action hypotheses give literal three-path
stabilizer transitivity.  The local action is retained here as the already
proved edge action interface; source-specific callers discharge it from the
linear and Suzuki marked orbit theorems. -/
theorem source_three_path_stabilizer_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hprod : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      Q (family P) v ⊔ Q (family P) w =
        (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hlocal : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
      (graph (family P)).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y)
    {beta : Vertex (family P)} {p q : BasedWalk (graph (family P)) 3 beta}
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking) :
    ∃ g ∈ stabilizer (family P) beta,
      p.vertices.map (g • ·) = q.vertices := by
  let F := family P
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
  obtain ⟨g,hg,hgu⟩ := d.transitive beta ⟨u,huv⟩ ⟨u',huv'⟩
  change g • u = u' at hgu
  have hgb : g • beta = beta := d.local_le beta hg
  have hgv : (graph F).Adj (g • u) (g • v) := by
    exact (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr huv2
  have hgv' : (graph F).Adj u' (g • v) := by rwa [hgu] at hgv
  have hgne : g • v ≠ beta := fun he =>
    hne2 (MulAction.injective g (he.trans hgb.symm))
  obtain ⟨k,hk,hkv⟩ := hlocal u' beta huv'.symm (g • v) v' hgv' huv2' hgne hne2'
  have hku : k • u' = u' := d.local_le u' hk.1
  have hkb : k • beta = beta := hk.2
  have hkvx : (graph F).Adj v' ((k*g) • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F (k*g)).map_adj_iff.mpr hvx
    change (graph F).Adj ((k*g) • v) ((k*g) • x) at hh
    simpa only [mul_smul,hkv] using hh
  have hkn : (k*g) • x ≠ u' := fun he => hne2u (by
    apply MulAction.injective (k*g)
    calc
      (k*g) • x = u' := he
      _ = (k*g) • u := by simp only [mul_smul, hgu, hku])
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d huv2'.symm
  obtain ⟨t,ht,htx⟩ := source_full_product_core_transitive h d huv2'.symm
    (models v') R hR (hprod v' u' huv2'.symm) (hlocal v' u' huv2'.symm)
    hkvx hvx' hkn hne2u'
  have htfix : t • beta = beta :=
    ((source_Z_Q_U h u').2.trans ((ballKernel_one_le_edge F huv'.symm).trans inf_le_right)) ht
  have htfix_u' : t • u' = u' := Q_le_stabilizer F u' ht
  have htfix_v' : t • v' = v' :=
    ((source_Z_Q_U h u').2.trans ((ballKernel_one_le_edge F huv2').trans inf_le_right)) ht
  have hfix : (k*g) • beta = beta := by rw [mul_smul,hgb,hkb]
  refine ⟨t*(k*g), ?_, ?_⟩
  · change (t*(k*g)) • beta = beta
    rw [mul_smul,hfix,htfix]
  · simp only [BasedWalk.vertices, List.map_cons, List.map_nil, mul_smul, hgb, hgu,
      hkb, hku, hkv, htfix, htfix_u', htfix_v']
    have hlast : t • k • g • x = x' := by
      rw [← mul_smul k g]
      exact htx
    simp only [hlast]

/-- Transport a source critical pair to a prescribed nonbacktracking
three-path endpoint. -/
theorem source_critical_pair_on_three_path
    {F : Bool → Subgroup G} [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    {a a' x : Vertex F} (hc : IsCriticalPair F a a')
    (hb : b F = 3) (target : BasedWalk (graph F) 3 x)
    (htarget : target.Nonbacktracking)
    (ht : RootPathTransitive (graph F) G (base F x.type) 3)
    (hx : x.type = a.type) : IsCriticalPair F x target.endpoint := by
  let hact : GraphAction (graph F) G :=
    ⟨fun g _ _ hadj =>
      (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj hadj⟩
  obtain ⟨g,hg⟩ := (same_orbit_iff F a x).mpr hx.symm
  have hc' := criticalPair_translate F hc g
  obtain ⟨g₀,hg₀⟩ := (same_orbit_iff F (base F x.type) x).mpr rfl
  have hroot : RootPathTransitive (graph F) G x 3 := by
    simpa only [hg₀] using
      SimpleGraph.PathTransitivePolygon.RootPathTransitive.smul hact ht g₀
  obtain ⟨w,hw,hwlen⟩ := (connected F hgen).exists_path_of_dist x (g • a')
  have hwlen3 : w.length = 3 := hwlen.trans (by simpa [hg, hb] using hc'.1)
  let q : BasedWalk (graph F) 3 x := hwlen3 ▸ BasedWalk.ofWalk w
  have hq : q.Nonbacktracking := by
    simpa only [q] using (BasedWalk.nonbacktracking_cast hwlen3 _).mpr
      (nonbacktracking_ofWalk_of_isPath w hw)
  have hqend : q.endpoint = g • a' := by
    simp only [q, BasedWalk.endpoint_cast, endpoint_ofWalk] at hwlen ⊢
  obtain ⟨u,hu,hus⟩ := hroot q target hq htarget
  have he := criticalPair_translate F hc' u
  have hend := endpoint_smul_of_vertices hact u q target hus
  rw [hqend] at hend
  have hux : u • g • a = x := by rw [hg]; exact hu
  simpa only [hux, hend] using he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
