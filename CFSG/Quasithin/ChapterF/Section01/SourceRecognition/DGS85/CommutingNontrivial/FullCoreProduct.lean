module
public import Theory.GroupAction.SylowNormalizerOrbit
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Valence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood

/-!
# The full adjacent-core product in the radius-three argument

If the adjacent cores fill the full edge two-core, Sylow transitivity on
the other neighbors supplies a core transporter fixing the earlier path
vertices. Two local transporters and this core transporter make the
radius-three sphere transitive under its original vertex stabilizer.

At b = 5, 8.4(1) places W = V_beta^(3) in the predecessor core. That
predecessor's center is central in W. Sphere transitivity propagates this
to every radius-three seed; short-distance commutation treats radius one,
and the central vertex orbit of 8.1(a) treats radius two. Consequently W
itself is elementary, so its literal intersection with Q_alpha' is too.
`FullCoreDistance` discharges the local action premises and applies 8.3
and the actual residual-section contradiction for the full catalogue.

Source: DGS, *Groups and Graphs* (1985), 8.1(a), 8.4, pp.132--138. This
uses the source's sphere-centrality argument with an explicitly proved
binary full-core-product action. It assumes neither a tree nor that an
arbitrary involution-generated intersection is elementary.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original full-edge two-core acts transitively on the other neighbors,
using the marked local Sylow normalizer and its two-power branching. -/
theorem source_edge_sylow_transitive_of_edge_transitive
    (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hR : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (ht : ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
      (graph (family P)).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y)
    {x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y) (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ g ∈ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2,
      g • x = y := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  have hstab : MulAction.stabilizer L w = normalizer (R : Set L) :=
    (source_edge_local_normalizer h d hvw M R hR).2
  have hbranch : ∃ n : ℕ, (normalizer (R : Set L)).index - 1 = 2^n := by
    have hh := M.sylow_normalizer_branching (quotientSylow R)
    have he := quotientSylow_normalizer_comap R
    simp only [Sylow.coe_coe] at he
    rw [←he,index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hh
  have horbit {z : Vertex F} (hz : (graph F).Adj v z) : z ∈ MulAction.orbit L w := by
    obtain ⟨g,hg,hgz⟩ := d.transitive v ⟨w,hvw⟩ ⟨z,hz⟩
    exact ⟨⟨g,hg⟩,hgz⟩
  have hadj {z : Vertex F} (hz : z ∈ MulAction.orbit L w) : (graph F).Adj v z := by
    obtain ⟨g,rfl⟩ := hz
    have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr hvw
    change (graph F).Adj ((g : G) • v) ((g : G) • w) at hh
    rwa [show (g : G) • v = v from d.local_le v g.property] at hh
  obtain ⟨g,hg,hgxy⟩ := Theory.GroupAction.sylow_transitive_away_from_base R w hstab hbranch (by
    intro z hz t ht' hzw htw
    obtain ⟨g,hg,he⟩ := ht z t (hadj hz) (hadj ht') hzw htw
    refine ⟨⟨g,hg.1⟩,?_,he⟩
    rw [←hstab]
    exact hg.2) (horbit hx) (horbit hy) hxw hyw
  exact ⟨g,hR ▸ mem_map_of_mem L.subtype hg,hgxy⟩

/-- When the adjacent cores fill the full edge two-core, the opposite
vertex core itself acts transitively on the other neighbors. -/
theorem source_full_product_core_transitive
    (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hR : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hprod : Q (family P) v ⊔ Q (family P) w =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (ht : ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
      (graph (family P)).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y)
    {x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y) (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ g ∈ Q (family P) w, g • x = y := by
  let := finite_endpoints h
  let F := family P
  obtain ⟨g,hg,hgxy⟩ := source_edge_sylow_transitive_of_edge_transitive h d hvw M R hR ht hx hy hxw hyw
  have hn : Q F w ≤ normalizer (Q F v : Set G) :=
    ((source_Z_Q_U h w).2.trans ((ballKernel_one_le_edge F hvw.symm).trans inf_le_right)).trans
      (stabilizer_normalizes_Q F v)
  have hm : g ∈ (Q F w ⊔ Q F v : Subgroup G) := by rw [sup_comm,hprod]; exact hg
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hn] at hm
  obtain ⟨c,hc,t,ht',rfl⟩ := hm
  have htx : t • x = x :=
    ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F hx).trans inf_le_right)) ht'
  exact ⟨c,hc,by simpa only [mul_smul,htx] using hgxy⟩

/-- One full adjacent-core product transports to every original edge,
including the reversed orientation. -/
theorem source_full_core_product_all_edges
    (F : Bool → Subgroup G)
    {a beta : Vertex F} (hab : (graph F).Adj a beta)
    (hprod : Q F a ⊔ Q F beta = (stabilizer F a ⊓ stabilizer F beta).pCoreIn 2)
    {v w : Vertex F} (hvw : (graph F).Adj v w) :
    Q F v ⊔ Q F w = (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 := by
  have direct {a beta v w : Vertex F} (hab : (graph F).Adj a beta)
      (hvw : (graph F).Adj v w) (ht : a.type = v.type)
      (hp : Q F a ⊔ Q F beta = (stabilizer F a ⊓ stabilizer F beta).pCoreIn 2) :
      Q F v ⊔ Q F w = (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 := by
    have ht' : beta.type = w.type := by
      have h1 := hab.1
      have h2 := hvw.1
      cases ha : a.type <;> cases hb : beta.type <;> cases hv : v.type <;>
        cases hw : w.type <;> simp_all
    obtain ⟨g,hga,hgb⟩ := incident_common_translate F hab.2
    obtain ⟨t,htv,htw⟩ := incident_common_translate F hvw.2
    let u := t*g⁻¹
    have hua : u • a = v := by rw [←hga]; simp only [u,mul_smul,inv_smul_smul,ht,htv]
    have hub : u • beta = w := by rw [←hgb]; simp only [u,mul_smul,inv_smul_smul,ht',htw]
    have hh := congrArg (fun H : Subgroup G => H.map (MulAut.conj u).toMonoidHom) hp
    rw [Subgroup.map_sup,←Q_translate,←Q_translate,
      ←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj u).injective,
      map_inf _ _ _ (MulAut.conj u).injective,←stabilizer_translate,←stabilizer_translate,hua,hub] at hh
    exact hh
  by_cases he : a.type = v.type
  · exact direct hab hvw he hprod
  · have he' : beta.type = v.type := by
      have hh := hab.1
      cases ha : a.type <;> cases hb : beta.type <;> cases hv : v.type <;> simp_all
    apply direct hab.symm hvw he'
    simpa only [sup_comm,inf_comm] using hprod

/-- Successive original local and core transporters give transitivity on
the distance-three sphere while fixing its center. -/
theorem source_full_product_sphere_three_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hprod : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      Q (family P) v ⊔ Q (family P) w =
        (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (ht : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
      (graph (family P)).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y)
    {beta x y : Vertex (family P)}
    (hx : (graph (family P)).dist beta x = 3)
    (hy : (graph (family P)).dist beta y = 3) :
    ∃ g ∈ stabilizer (family P) beta, g • x = y := by
  let := finite_endpoints h
  let F := family P
  have path {z : Vertex F} (hz : (graph F).dist beta z = 3) :
      ∃ u v : Vertex F, (graph F).Adj beta u ∧ (graph F).Adj u v ∧
        (graph F).Adj v z ∧ beta ≠ v ∧ u ≠ z := by
    obtain ⟨v,hvz,hdv⟩ := exists_predecessor F h.generate beta z (by intro he; simp [he] at hz)
    have hdv' : (graph F).dist beta v = 2 := by omega
    obtain ⟨u,huv,hdu⟩ := exists_predecessor F h.generate beta v (by intro he; simp [he] at hdv')
    refine ⟨u,v,SimpleGraph.dist_eq_one_iff_adj.mp (by omega),huv.symm,hvz.symm,?_,?_⟩
    · intro he; simp [he] at hdv'
    · intro he; rw [he] at hdu; omega
  obtain ⟨u,v,hbu,huv,hvx,hbv,hux⟩ := path hx
  obtain ⟨u',v',hbu',huv',hv'y,hbv',hu'y⟩ := path hy
  obtain ⟨g,hg,hgu⟩ := d.transitive beta ⟨u,hbu⟩ ⟨u',hbu'⟩
  have hgb : g • beta = beta := d.local_le beta hg
  have hgadj : (graph F).Adj u' (g • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr huv
    change (graph F).Adj (g • u) (g • v) at hh
    rwa [hgu] at hh
  have hgne : g • v ≠ beta := fun he => hbv
    ((MulAction.injective g) (hgb.trans he.symm))
  obtain ⟨k,hk,hkv⟩ := ht u' beta hbu'.symm (g • v) v' hgadj huv' hgne hbv'.symm
  have hkβ : k • beta = beta := hk.2
  have hku : k • u' = u' := d.local_le u' hk.1
  have hxadj : (graph F).Adj v' ((k*g) • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F (k*g)).map_adj_iff.mpr hvx
    change (graph F).Adj ((k*g) • v) ((k*g) • x) at hh
    simpa only [mul_smul,hkv] using hh
  have hxne : (k*g) • x ≠ u' := by
    intro he
    apply hux
    apply MulAction.injective (k*g)
    simpa only [mul_smul,hgu,hku] using he.symm
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d huv'.symm
  obtain ⟨t,htQ,htx⟩ := source_full_product_core_transitive h d huv'.symm (models v') R hR
    (hprod v' u' huv'.symm) (ht v' u' huv'.symm) hxadj hv'y hxne hu'y.symm
  have htβ : t • beta = beta :=
    ((source_Z_Q_U h u').2.trans ((ballKernel_one_le_edge F hbu'.symm).trans inf_le_right)) htQ
  exact ⟨t*(k*g),by change (t*(k*g)) • beta = beta; rw [mul_smul,mul_smul,hgb,hkβ,htβ],
    by rw [mul_smul]; exact htx⟩

/-- At distance five, a full adjacent-core product makes the original
radius-three span elementary. The central sphere seed comes from 8.4(1);
the radius-two seeds use the central vertex orbit from 8.1(a). -/
theorem source_full_product_radius_three_elementary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : b (family P) = 5) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥)
    (hprod : Q (family P) a ⊔ Q (family P) beta =
      (stabilizer (family P) a ⊓ stabilizer (family P) beta).pCoreIn 2)
    (ht : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
      (graph (family P)).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y) :
    IsElementaryAbelian 2 (V (family P) beta 3) := by
  let := finite_endpoints h
  let F := family P
  let W := V F beta 3
  have hb' : b F = 5 := hb
  have hZ := fun v => (source_Z_Q_U h v).1
  obtain ⟨prev,hprev,hdprev,hWprev⟩ := source_radius_three_core h hB d hob models hc hab hd
    (by omega) hcomm hne
  have hdprev' : (graph F).dist beta prev = 3 := by
    change (graph F).dist beta a' + 1 = b F at hd
    change (graph F).dist beta prev + 1 = (graph F).dist beta a' at hdprev
    omega
  have hbase : Z F prev ≤ centralizer (W : Set G) :=
    (Z_centralizes_Q F prev (hZ prev)).trans (centralizer_le hWprev)
  have hcent : ∀ z, z ∈ ball F beta 3 → Z F z ≤ centralizer (W : Set G) := by
    intro z hz
    have hdz := (mem_ball_iff F h.generate beta z 3).mp hz
    by_cases hnear : (graph F).dist beta z ≤ 1
    · have hZV : Z F z ≤ V F beta 1 := le_iSup_of_le z
        (le_iSup_of_le ((mem_ball_iff F h.generate beta z 1).mpr hnear) le_rfl)
      exact hZV.trans (radius_spans_centralize F h.generate hZ d.kernel_sylow beta 1 3 (by omega))
    by_cases htwo : (graph F).dist beta z = 2
    · have htype : beta.type = z.type := (even_dist_iff F h.generate beta z).mp (by rw [htwo]; decide)
      obtain ⟨g,hgz⟩ := (same_orbit_iff F beta z).mpr htype
      have hcbeta := (source_critical_geometry h d hc hab hd (by omega) hcomm).2.2.1
      have hcz : Z F z = omegaCenterIn (d.localGroup z) := by
        rw [←hgz,Z_translate,d.conjugate,
          ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hcbeta]
      have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer F beta)).to_le
        (V_le_Q_of_dist_add_lt_b F h.generate hZ beta beta 3 (by simpa using (show 3 < b F by omega))
          (d.kernel_sylow beta))
      have hWL : W ≤ d.localGroup z := pGroup_le_localGroup F d z W hpW
        (V_le_stabilizer_of_dist_add_le_b F h.generate beta z 3 (by omega))
      intro x hx y hy
      have hxO : x ∈ omegaCenterIn (d.localGroup z) := hcz ▸ hx
      exact ((mem_omegaCenterIn_iff _ _).mp hxO).2.1 y (hWL hy)
    · have hthree : (graph F).dist beta z = 3 := by omega
      obtain ⟨g,hgb,hgz⟩ := source_full_product_sphere_three_transitive h hB d models
        (fun v w hvw => source_full_core_product_all_edges F hab hprod hvw) ht hdprev' hthree
      intro x hx y hy
      have hx' : g⁻¹*x*g ∈ Z F prev := by
        have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx
        rw [←Z_translate,←hgz,inv_smul_smul] at hh
        change g⁻¹*x*g⁻¹⁻¹ ∈ Z F prev at hh
        simpa only [inv_inv] using hh
      have hy' : g⁻¹*y*g ∈ W := by
        have hgn : g⁻¹ ∈ normalizer (W : Set G) :=
          (normalizer (W : Set G)).inv_mem (stabilizer_normalizes_V F beta 3 hgb)
        simpa only [inv_inv] using le_normalizer_iff.mp le_rfl _ hgn y hy
      have he := hbase hx' _ hy'
      have he' := congrArg (fun t : G => g*t*g⁻¹) he
      simpa [mul_assoc] using he'
  let E : ball F beta 3 → Subgroup G := fun z => Z F z.val
  let : ∀ z, IsElementaryAbelian 2 (E z) := fun z => CommutingOneProfile.source_center_elementary h z.val
  have he : W = ⨆ z, E z := by
    apply le_antisymm
    · apply iSup_le; intro z; apply iSup_le; intro hz; exact le_iSup E ⟨z,hz⟩
    · apply iSup_le; intro z; exact le_iSup_of_le z.val (le_iSup_of_le z.property le_rfl)
  change IsElementaryAbelian 2 W
  rw [he]
  apply IsElementaryAbelian.iSup_of_le_centralizer E
  intro z t
  exact (hcent z.val z.property).trans (centralizer_le
    (show E t ≤ W from le_iSup_of_le t.val (le_iSup_of_le t.property le_rfl)))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
