module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.GeometryInputs

/-!
# The kernel deduction in the equal-Z case of MS93 (4.5.5)

Write c=a+2, d=a+4, e=a+6, and delta=c^g for g in G_a. If
Z_c lies in Z_a Z_delta, the actual conjugate of hat W_c centralizes Z_c:
it lies in both Q_a and Q_delta by the radius bounds. It also lies in the
edge kernel Q_beta through Q_a. The literal common centralizer identity
therefore puts it in Q_c. The preceding (4.5.3) commutator bound now gives
the stronger bound by Z_c required in the equal-Z case.

The last two deductions combine this calculation with the literal unequal-Z
product intersection and apply the result in `LocalBounds`. The geometric
containment, product intersection, and opening noncentrality still require
proof. They are explicit obligations, not established source conclusions.
Earlier (4.5.1)--(4.5.3) and the marked section have their existing producers;
this module does not use the erroneous legacy `Early.OrbitFacts` record.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The equal-Z branch after its source geometric containment is supplied.
The conjugate remains the literal conjugate of the entire original seed. -/
theorem pair_bound_of_Z_le_join [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a)
    (hZ : Z R (p.walk.getVert 6) ≤ Z R a ⊔ Z R (act R g (p.walk.getVert 6)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)) :
    ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
        Z R (p.walk.getVert 6) := by
  let c := p.walk.getVert 6
  let d := p.walk.getVert 8
  let e := p.walk.getVert 10
  let t := p.walk.getVert 5
  let A := rightConjugate (hatW R c d e) g
  have hc : color R c = false :=
    (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have ha : color R a = false := by
    rw [← p.center_eq]
    exact (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hct : Adjacent R c t := by
    apply adjacent_symm R
    exact (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; decide))
  have hat : Adjacent R a t := by
    rw [← p.center_eq]
    exact (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; decide))
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hAqa : A ≤ Q R a := by
    have hseed := (hatW_seed_le_hatSix a c d e).trans (p.hatSix_le_Q earlier)
    exact (map_mono hseed).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (Q_normalized R a ((stabilizer R a).inv_mem g.property))).le
  have hAqd : A ≤ Q R (act R g c) := by
    rw [show A = hatW R (act R g c) (act R g d) (act R g e) from
      rightConjugate_hatW g c d e]
    exact (hatW_le_radius R (by rw [dist_act]; exact p.two_step_distances.2.1.le)
      (by rw [dist_act]; exact p.two_step_distances.2.2.le)).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q _
        (by rwa [action_preserves_color]) 4 (by rw [earlier.distance]; decide))
  have hAcZa : A ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    hAqa.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)))
  have hAcZd : A ≤ centralizer (Z R (act R g c) : Set (FreeAmalgam R)) := by
    have hgcol : color R (act R g c) = false := by rwa [action_preserves_color]
    exact hAqd.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hgcol)))
  have hAcZ : A ≤ centralizer (Z R c : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    exact hZ.trans (sup_le (le_centralizer_iff.mp hAcZa) (le_centralizer_iff.mp hAcZd))
  have hAqc : A ≤ Q R c := by
    rw [← common.centralizer c t hc hct]
    exact le_inf (hAqa.trans (Q_le_adjacent_h R ht hat)) hAcZ
  exact (commutator_mono le_rfl hAqc).trans hW

/-- The source case split, with its remaining geometric assertions explicit.
In the equal-Z case the proof gives the stronger bound by Z_(a+2). -/
theorem pair_bounds_of_Z_geometry [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (facts : ZCaseGeometry p)
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)) :
    ∀ g : stabilizer R a,
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R a (p.walk.getVert 6) := by
  intro g
  by_cases hz : Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5))
  · have hjoin : Z R (p.walk.getVert 6) ≤
        Z R a ⊔ Z R (act R g (p.walk.getVert 6)) := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := facts.equal_Z_span g hz hx
      exact (Z R a ⊔ Z R (act R g (p.walk.getVert 6))).mul_mem
        (mem_sup_left hu) (mem_sup_right hv)
    exact (pair_bound_of_Z_le_join source common earlier p g hjoin hW).trans
      (Z_le_localZSpan R _ _)
  · intro x hx
    have h := facts.unequal_Z_commutator g hz hx
    rw [facts.unequal_Z_intersection g hz] at h
    exact h

/-- Actual application to both commutator equalities in (4.5.5). The three
Z-case geometric assertions and opening noncentrality remain explicit;
the preceding source inputs retain their independent producers. -/
theorem commutator_layers_of_Z_geometry [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6))
    (sectionModel : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (facts : ZCaseGeometry p)
    (hnon : ¬ ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≤ Z R (alpha R)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) := by
  have hpairs := pair_bounds_of_Z_geometry source common earlier p facts hW
  exact SourcePath.commutator_layers_of_pair_bounds source common earlier p
    hVa hVd hleft hright hW sectionModel hpairs hnon

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
