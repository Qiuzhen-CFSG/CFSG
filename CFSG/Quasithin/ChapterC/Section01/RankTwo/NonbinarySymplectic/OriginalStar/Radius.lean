module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.CriticalActors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalSeed
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalSeed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarAbelian
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarComparison

/-!
# The original star inside the critical radius

The original critical action is inner and therefore centralizes each full
Sylow seed that it normalizes. Critical reversal and the exact vertex
centralizer place that seed in each core inside the critical radius. The
holomorph orbit span inherits these bounds, including own-core containment
and fixation of the critical endpoint. At distance at least four the entire
star is commutative and its endpoint action is quadratic.

The internal import reuses the generic critical-cover calculation within the
same source family. All conclusions concern the original radical and graph;
no minimum replacement or equality of critical distances is assumed.
Source: MS93 (3.4), printed p.868.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

theorem Input.original_critical_centralizes_normalized_sylow_seed
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (P : Sylow 2 (Ltilde R z))
    (hn : Z R a ≤ normalizer ((U R z ⊓ centralizer
      ((P : Subgroup (Ltilde R z)).map (Ltilde R z).subtype : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set _)) :
    Z R a ≤ centralizer (U R z ⊓ centralizer
      ((P : Subgroup (Ltilde R z)).map (Ltilde R z).subtype : Set (FreeAmalgam R)) :
        Set (FreeAmalgam R)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  exact critical_seed_central_of_ambient_cover path hb s e he j hj hjr κ hκQ hκL hconj
    (h.original_critical_image_inner path hb) P hn

theorem Input.original_sylow_seed_le_core_of_distance
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {u c t : Vertex R} (hd : color R u = false) (hcc : color R c = false)
    (hdc : (cosetGraph R).dist u c ≤ geometry.b R)
    (hct : (cosetGraph R).dist c t < geometry.b R)
    (P : Sylow 2 (Ltilde R u))
    (hn : Q R t ≤ normalizer ((U R u ⊓ centralizer
      ((P : Subgroup (Ltilde R u)).map (Ltilde R u).subtype : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set _)) :
    U R u ⊓ centralizer
      ((P : Subgroup (Ltilde R u)).map (Ltilde R u).subtype : Set (FreeAmalgam R)) ≤ Q R c := by
  by_cases hz : Z R u ≤ Q R c
  · exact (inf_le_left.trans (U_le_Z u)).trans hz
  have hcrit : CriticalPair R u c (geometry.exists_critical u hd) := by
    refine ⟨le_antisymm ?_ (criticalDistance_le R u _ hz),hz⟩
    rwa [geometry.distance_constant u hd]
  have hedge := MSCentralOrbit.edgeCentralizerCondition R (h.radical.isPGroup)
    (h.radical.twoCore_le) (h.omegaOrbit_centralizer)
  have hrev := critical_reverse R geometry hedge u hd
    (by rwa [geometry.distance_constant u hd]) c hcc hcrit
  obtain ⟨walk,hwalk⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c u
  let path : CriticalPath R geometry c u := ⟨hcc,walk,hwalk,hrev⟩
  have hZt : Z R c ≤ Q R t := Z_le_Q_of_dist_lt R c (geometry.exists_critical c hcc)
    (by rwa [geometry.distance_constant c hcc])
  have hcentral := h.original_critical_centralizes_normalized_sylow_seed path hb P (hZt.trans hn)
  rw [←MSCentralOrbit.C_eq_Q R (h.radical.isPGroup)
    (h.radical.twoCore_le) (h.omegaOrbit_centralizer) c hcc]
  exact le_inf
    ((inf_le_left.trans (U_le_Z u)).trans
      (Z_le_stabilizer_of_dist_le u (geometry.exists_critical u hd) hcrit.1.le))
    (le_centralizer_iff.mp hcentral)

theorem Input.original_two_edge_sylow_seed_le_distant_core
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {a u c t : Vertex R} (hd : color R u = false) (hcc : color R c = false)
    (hat : Adjacent R a t) (hdt : Adjacent R u t)
    (hac : (cosetGraph R).dist a c + 2 ≤ geometry.b R)
    (P : Sylow 2 (Ltilde R u))
    (hn : Q R t ≤ normalizer ((U R u ⊓ centralizer
      ((P : Subgroup (Ltilde R u)).map (Ltilde R u).subtype : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set _)) :
    U R u ⊓ centralizer
      ((P : Subgroup (Ltilde R u)).map (Ltilde R u).subtype : Set (FreeAmalgam R)) ≤ Q R c := by
  have hdt1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
  have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have htac := (cosetGraph_connected R).dist_triangle (u := t) (v := a) (w := c)
  have hdtc := (cosetGraph_connected R).dist_triangle (u := u) (v := t) (w := c)
  have hta1 : (cosetGraph R).dist t a = 1 := by rwa [SimpleGraph.dist_comm]
  rw [hta1] at htac
  have hdc : (cosetGraph R).dist u c ≤ geometry.b R := by omega
  have hct : (cosetGraph R).dist c t < geometry.b R := by
    rw [SimpleGraph.dist_comm]
    omega
  exact h.original_sylow_seed_le_core_of_distance geometry hb hd hcc hdc hct P hn



theorem Input.original_sourceStarAlpha_le_distant_core
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    {c : Vertex R} (hcc : color R c = false)
    (hac : (cosetGraph R).dist (alpha R) c + 2 ≤ geometry.b R) :
    sourceStarAlpha R Y ≤ Q R c := by
  have hbeta : (starSpan R Y).map (embedS R) =
      (⨆ h : Hbar R, (Y.map (embedS R)).map (MulAut.conj (h : FreeAmalgam R)).toMonoidHom) ⊔
        Z R (beta R) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
  have hZaQ : Z R (alpha R) ≤ Q R c := Z_le_Q_of_dist_lt R (alpha R)
    (geometry.exists_critical (alpha R) rfl) (by
      rw [geometry.distance_constant (alpha R) rfl]
      change (cosetGraph R).dist (alpha R) c < geometry.b R
      omega)
  apply (sourceStarAlpha_le_iff R Y _).mpr
  intro g
  rw [hbeta,Subgroup.map_sup,Subgroup.map_iSup]
  apply sup_le
  · apply iSup_le
    intro k
    obtain ⟨P',hP',hn'⟩ := transported_seed_is_componentSylowSeed R Y P hY hn g k
    obtain ⟨hat,hdt⟩ := transported_seed_edges R g k
    rw [hP']
    exact h.original_two_edge_sylow_seed_le_distant_core geometry hb
      (by simp only [action_preserves_color]; rfl) hcc hat hdt hac P' hn'
  · have hg : (g : FreeAmalgam R) ∈ stabilizer R (alpha R) := by
      simpa only [alpha,stabilizer_m_base] using g.property
    have hfix := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hg)
    have hba : Z R (beta R) ≤ Z R (alpha R) := by
      change edgeOmega R (beta R) ≤ ⨆ b, ⨆ (_ : Adjacent R (alpha R) b), edgeOmega R b
      exact le_iSup_of_le (beta R) (le_iSup_of_le (base_adjacent R) le_rfl)
    exact ((map_mono hba).trans_eq hfix).trans hZaQ

theorem Input.original_sourceStarAlpha_le_own_core
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    sourceStarAlpha R Y ≤ Q R (alpha R) := by
  have heven := geometry.even (alpha R) rfl
  rw [geometry.distance_constant (alpha R) rfl] at heven
  change Even (geometry.b R) at heven
  obtain ⟨n,hnn⟩ := heven
  exact h.original_sourceStarAlpha_le_distant_core geometry hb Y P hY hn rfl (by simp only [SimpleGraph.dist_self]; omega)


/-- The actual star fixes the far endpoint of every critical path. -/
theorem Input.original_sourceStarAlpha_le_critical_endpoint_stabilizer
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    sourceStarAlpha R Y ≤ stabilizer R z := by
  apply le_endpoint_stabilizer_of_radius_core_bound path hb
  intro c hc hac
  exact h.original_sourceStarAlpha_le_distant_core geometry hb Y P hY hn hc hac

/-- In the large-distance branch of the original graph the source star is abelian, including every
fixed central attachment in its generating Sylow seed. -/
theorem Input.original_sourceStarAlpha_commutative_of_four_le
    (geometry : Geometry R) (hfour : 4 ≤ geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    IsMulCommutative (sourceStarAlpha R Y) := by
  apply sourceStarAlpha_commutative_of_radius_core_bounds R geometry (by omega) Y
    (hY.le.trans inf_le_left)
  intro c hc hdist
  exact h.original_sourceStarAlpha_le_distant_core geometry (by omega)
    Y P hY hn hc (by omega)

/-- The full star acts quadratically on the critical endpoint layer. This
is a statement about the literal subgroup commutator, before any quotient. -/
theorem Input.original_sourceStarAlpha_quadratic
    (geometry : Geometry R) (hfour : 4 ≤ geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    ⁅⁅Z R z,sourceStarAlpha R Y⁆,sourceStarAlpha R Y⁆ = ⊥ := by
  let := h.original_sourceStarAlpha_commutative_of_four_le geometry hfour Y P hY hn
  have hZA : Z R z ≤ stabilizer R (alpha R) := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant (alpha R) rfl,
      geometry.distance_constant z path.end_color]
  have hcomm : ⁅Z R z,sourceStarAlpha R Y⁆ ≤ sourceStarAlpha R Y :=
    le_normalizer_iff_commutator_le_right.mp
      (hZA.trans (sourceStarAlpha_normalized R Y))
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hcomm.trans (sourceStarAlpha R Y).le_centralizer)


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
