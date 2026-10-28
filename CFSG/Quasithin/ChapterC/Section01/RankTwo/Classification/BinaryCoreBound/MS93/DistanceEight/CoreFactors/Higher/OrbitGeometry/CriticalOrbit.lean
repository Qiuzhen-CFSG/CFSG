module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path

/-!
# The critical orbit reduction in MS93 (4.5.4)(ii)

For a vertex d within four steps of a, every G_a-conjugate of d is within
eight steps of d. If the Z_d orbit span misses Q_d, one of its generators
therefore gives a critical pair. Conversely an abelian orbit span cannot
contain the two noncommuting Z-layers of that critical pair. Containment in
Q_d makes the seed central in its orbit span, hence makes the whole span
abelian by conjugation.

These results justify the opening reduction and the printed "i.e." in
(4.5.4)(ii). The subsequent critical replacement and unequal-Z contradiction
on pp.898--899 remain separate geometric obligations.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem seed_le_span {G : Type*} [Group G] (A P : Subgroup G) :
    A ≤ conjugatesIn A P := by
  intro x hx
  apply (le_iSup (fun g : P => rightConjugate A g) 1)
  exact ⟨x, hx, by simp⟩

private theorem span_abelian_of_seed_central {G : Type*} [Group G]
    (A P : Subgroup G) (h : ⁅A, conjugatesIn A P⁆ = ⊥) :
    IsMulCommutative (conjugatesIn A P) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply iSup_le
  intro g
  apply commutator_eq_bot_iff_le_centralizer.mp
  have hn := mem_normalizer_iff_map_conj_eq.mp
    (conjugatesIn_normalized A P (P.inv_mem g.property))
  have hm := congrArg (fun D : Subgroup G =>
    D.map (MulAut.conj (g : G)⁻¹).toMonoidHom) h
  simpa only [map_commutator, MulEquiv.toMonoidHom_eq_coe, hn, Subgroup.map_bot,
    rightConjugate] using hm

/-- Containment in Q_d centralizes the seed Z_d, hence every orbit generator.
This is the easy direction of the printed equivalence in (4.5.4)(ii). -/
theorem orbit_abelian_of_le_Q [Finite M] {a d : Vertex R} (hd : color R d = false)
    (h : conjugatesIn (Z R d) (stabilizer R a) ≤ Q R d) :
    IsMulCommutative (conjugatesIn (Z R d) (stabilizer R a)) := by
  apply span_abelian_of_seed_central
  exact le_bot_iff.mp ((commutator_mono le_rfl h).trans (Z_centralizes_Q R d hd).le)

/-- A missing Q_d containment produces the actual critical pair used at the
start of the proof of (4.5.4)(ii), with the original right action. -/
theorem exists_critical_of_orbit_not_le_Q (earlier : Earlier R geometry)
    {a d : Vertex R} (hd : color R d = false)
    (hda : (cosetGraph R).dist d a ≤ 4)
    (hn : ¬ conjugatesIn (Z R d) (stabilizer R a) ≤ Q R d) :
    ∃ g : stabilizer R a, CriticalPair R (act R g d) d
      (geometry.exists_critical _ ((action_preserves_color R g d).trans hd)) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : stabilizer R a, ¬ rightConjugate (Z R d) g ≤ Q R d := by
    by_contra h
    exact hn (iSup_le fun g => by simpa using not_exists.mp h g)
  have hcol : color R (act R g d) = false := (action_preserves_color R g d).trans hd
  have hnot : ¬ Z R (act R g d) ≤ Q R d := by
    simpa only [Z_act, rightConjugate] using hg
  have hb : criticalDistance R (act R g d) (geometry.exists_critical _ hcol) = 8 :=
    (geometry.distance_constant _ hcol).trans earlier.distance
  have hfixed : act R g a = a := g.property
  have hdist : (cosetGraph R).dist (act R g d) a ≤ 4 := by
    simpa only [hfixed] using (dist_act R (g : FreeAmalgam R) d a).le.trans hda
  have hupper : (cosetGraph R).dist (act R g d) d ≤ 8 := by
    have ht := (cosetGraph_connected R).dist_triangle
      (u := act R g d) (v := a) (w := d)
    rw [SimpleGraph.dist_comm (u := a) (v := d)] at ht
    omega
  have hlower : 8 ≤ (cosetGraph R).dist (act R g d) d := by
    by_contra h
    apply hnot
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcol)
    rw [hb]
    omega
  refine ⟨g, ?_, hnot⟩
  rw [hb]
  exact le_antisymm hupper hlower

/-- The two conclusions printed as equivalent in (4.5.4)(ii) really are
equivalent here; the reverse implication uses critical noncommutation. -/
theorem orbit_abelian_iff_le_Q [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a d : Vertex R} (hd : color R d = false)
    (hda : (cosetGraph R).dist d a ≤ 4) :
    IsMulCommutative (conjugatesIn (Z R d) (stabilizer R a)) ↔
      conjugatesIn (Z R d) (stabilizer R a) ≤ Q R d := by
  refine ⟨?_, orbit_abelian_of_le_Q hd⟩
  intro hab
  by_contra hn
  obtain ⟨g, hg⟩ := exists_critical_of_orbit_not_le_Q earlier hd hda hn
  apply common.critical_noncommutation _ ((action_preserves_color R g d).trans hd) d hg
  apply le_bot_iff.mp
  have hseed := seed_le_span (Z R d) (stabilizer R a)
  have hconj : Z R (act R g d) ≤ conjugatesIn (Z R d) (stabilizer R a) := by
    rw [Z_act]
    exact le_iSup (fun k : stabilizer R a => rightConjugate (Z R d) k) g
  exact (commutator_mono hconj hseed).trans (commutator_self_eq_bot_iff.mpr hab).le

/-- The critical witness at the literal d=a+4 of the supplied source path. -/
theorem SourcePath.critical_orbit_witness {a : Vertex R} (p : Higher.SourcePath a)
    (earlier : Earlier R geometry)
    (hn : ¬ conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R a) ≤
      Q R (p.walk.getVert 8)) :
    ∃ g : stabilizer R a,
      (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8 ∧
      ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8) := by
  have hd : color R (p.walk.getVert 8) = false :=
    (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hda : (cosetGraph R).dist (p.walk.getVert 8) a ≤ 4 := by
    have h := p.dist (i := 4) (j := 8) (by decide) (by decide)
    simpa only [p.center_eq, SimpleGraph.dist_comm] using h.le
  obtain ⟨g, hg⟩ := exists_critical_of_orbit_not_le_Q earlier hd hda hn
  refine ⟨g, ?_, hg.2⟩
  exact hg.1.trans ((geometry.distance_constant _
    ((action_preserves_color R g _).trans hd)).trans earlier.distance)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
