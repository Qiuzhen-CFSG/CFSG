module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalSeed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedChoice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarAbelian
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarComparison

/-!
# The source star on a nonbinary characteristic replacement

Transporting the literal full-Sylow fixed seed through the holomorph puts
the generated star inside all cores up to radius b-2. In particular it lies
in its own core and in the critical endpoint stabilizer. At distance at
least four, each generating seed centralizes the star, so the star is abelian.
The final constructor uses the seed supplied by the original odd-index
witness; no replacement radicality or field-four hypothesis is needed.

Source: MS93 (3.4), first paragraph of the star argument, p.868.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

theorem Input.replacement_sourceStarAlpha_le_distant_core
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical)=componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤ normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {c : Vertex d.radical} (hcc : color d.radical c = false)
    (hac : (cosetGraph d.radical).dist (alpha d.radical) c + 2 ≤ geometry.b d.radical) :
    sourceStarAlpha d.radical Y ≤ Q d.radical c := by
  have hbeta : (starSpan d.radical Y).map (embedS d.radical) =
      (⨆ h : Hbar d.radical, (Y.map (embedS d.radical)).map (MulAut.conj (h : FreeAmalgam d.radical)).toMonoidHom) ⊔
        Z d.radical (beta d.radical) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph d.radical Y
  have hZaQ : Z d.radical (alpha d.radical) ≤ Q d.radical c := Z_le_Q_of_dist_lt d.radical (alpha d.radical)
    (geometry.exists_critical (alpha d.radical) rfl) (by
      rw [geometry.distance_constant (alpha d.radical) rfl]
      change (cosetGraph d.radical).dist (alpha d.radical) c < geometry.b d.radical
      omega)
  apply (sourceStarAlpha_le_iff d.radical Y _).mpr
  intro g
  rw [hbeta,Subgroup.map_sup,Subgroup.map_iSup]
  apply sup_le
  · apply iSup_le
    intro k
    obtain ⟨P',hP',hn'⟩ := transported_seed_is_componentSylowSeed d.radical Y P hY hn g k
    obtain ⟨hat,hdt⟩ := transported_seed_edges d.radical g k
    rw [hP']
    exact h.replacement_two_edge_sylow_seed_le_distant_core d geometry hb
      (by simp only [action_preserves_color]; rfl) hcc hat hdt hac P' hn'
  · have hg : (g : FreeAmalgam d.radical) ∈ stabilizer d.radical (alpha d.radical) := by
      simpa only [alpha,stabilizer_m_base] using g.property
    have hfix := mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical (alpha d.radical) hg)
    have hba : Z d.radical (beta d.radical) ≤ Z d.radical (alpha d.radical) := by
      change edgeOmega d.radical (beta d.radical) ≤ ⨆ b, ⨆ (_ : Adjacent d.radical (alpha d.radical) b), edgeOmega d.radical b
      exact le_iSup_of_le (beta d.radical) (le_iSup_of_le (base_adjacent d.radical) le_rfl)
    exact ((map_mono hba).trans_eq hfix).trans hZaQ

theorem Input.replacement_sourceStarAlpha_le_own_core
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical)=componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤ normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    sourceStarAlpha d.radical Y ≤ Q d.radical (alpha d.radical) := by
  have heven := geometry.even (alpha d.radical) rfl
  rw [geometry.distance_constant (alpha d.radical) rfl] at heven
  change Even (geometry.b d.radical) at heven
  obtain ⟨n,hnn⟩ := heven
  exact h.replacement_sourceStarAlpha_le_distant_core d geometry hb Y P hY hn rfl (by simp only [SimpleGraph.dist_self]; omega)


/-- The actual star fixes the far endpoint of every critical path. -/
theorem Input.replacement_sourceStarAlpha_le_critical_endpoint_stabilizer
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    sourceStarAlpha d.radical Y ≤ stabilizer d.radical z := by
  apply le_endpoint_stabilizer_of_radius_core_bound path hb
  intro c hc hac
  exact h.replacement_sourceStarAlpha_le_distant_core d geometry hb Y P hY hn hc hac

/-- In the large-distance branch the source star is abelian, including every
fixed central attachment in its generating Sylow seed. -/
theorem Input.replacement_sourceStarAlpha_commutative_of_four_le
    (geometry : Geometry d.radical) (hfour : 4 ≤ geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    IsMulCommutative (sourceStarAlpha d.radical Y) := by
  apply sourceStarAlpha_commutative_of_radius_core_bounds d.radical geometry (by omega) Y
    (hY.le.trans inf_le_left)
  intro c hc hdist
  exact h.replacement_sourceStarAlpha_le_distant_core d geometry (by omega)
    Y P hY hn hc (by omega)

/-- The full star acts quadratically on the critical endpoint layer. This
is a statement about the literal subgroup commutator, before any quotient. -/
theorem Input.replacement_sourceStarAlpha_quadratic
    (geometry : Geometry d.radical) (hfour : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅⁅Z d.radical z,sourceStarAlpha d.radical Y⁆,sourceStarAlpha d.radical Y⁆ = ⊥ := by
  let := h.replacement_sourceStarAlpha_commutative_of_four_le d geometry hfour Y P hY hn
  have hZA : Z d.radical z ≤ stabilizer d.radical (alpha d.radical) := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant (alpha d.radical) rfl,
      geometry.distance_constant z path.end_color]
  have hcomm : ⁅Z d.radical z,sourceStarAlpha d.radical Y⁆ ≤ sourceStarAlpha d.radical Y :=
    le_normalizer_iff_commutator_le_right.mp
      (hZA.trans (sourceStarAlpha_normalized d.radical Y))
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hcomm.trans (sourceStarAlpha d.radical Y).le_centralizer)

/-- The source seed is constructed with its entire critical-radius bound.
This is the setup consumed by the remaining two star comparisons. -/
theorem Input.exists_replacement_star_radius
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical) :
    ∃ P : Sylow 2 (Ltilde d.radical (alpha d.radical)), ∃ Y : Subgroup d.radical,
      Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P ∧
      Q d.radical (beta d.radical) ≤
        normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)) ∧
      Nat.card (Y.map (embedS d.radical)) ≤ Nat.card F ^ 2 ∧
      (∀ c : Vertex d.radical, color d.radical c = false →
        (cosetGraph d.radical).dist (alpha d.radical) c + 2 ≤ geometry.b d.radical →
        sourceStarAlpha d.radical Y ≤ Q d.radical c) ∧
      (4 ≤ geometry.b d.radical → IsMulCommutative (sourceStarAlpha d.radical Y)) := by
  obtain ⟨P,Y,hY,hn,hcard,_⟩ := h.exists_replacement_source_seed d
  exact ⟨P,Y,hY,hn,hcard,
    fun _ hc hac => h.replacement_sourceStarAlpha_le_distant_core d geometry hb Y P hY hn hc hac,
    fun hfour => h.replacement_sourceStarAlpha_commutative_of_four_le d geometry hfour Y P hY hn⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
