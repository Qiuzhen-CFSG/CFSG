module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Geometry
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Join

/-!
# Actual carriers of the two single orbit quotients

Both orbit factors lie in the second hat layer, hence in Q_a. The first
hat layer centralizes the radius-four layer. Thus the literal abelianness
assertion (4.5.4)(ii) makes each enlarged orbit factor elementary abelian,
even though its definition includes the denominator explicitly.

The delta witness supplies its actual color, distance to c, and seed
containment. No recognition, order-eight or independence premise is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open NormalizerTransfer
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The original stabilizer normalizes the enlarged orbit factor. -/
theorem orbitFactor_normalized (p : Higher.SourcePath (alpha R)) (v : Vertex R) :
    stabilizer R (alpha R) ≤ normalizer (orbitFactor p v) :=
  (le_inf (conjugatesIn_normalized _ _) (hatV_normalized R _ _)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The denominator is contained literally, before forming any quotient. -/
theorem denominator_le (p : Higher.SourcePath (alpha R)) (v : Vertex R) :
    hatV R (alpha R) (p.walk.getVert 6) ≤ orbitFactor p v := le_sup_right

/-- Seed containment puts an orbit factor in the actual second layer. -/
theorem orbitFactor_le_second [Finite M] (p : Higher.SourcePath (alpha R))
    {v : Vertex R} (hv : Z R v ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8)) :
    orbitFactor p v ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  refine sup_le ?_ (lower_le_second p)
  apply iSup_le
  intro g
  exact (map_mono hv).trans (le_iSup (fun k : stabilizer R (alpha R) =>
      rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k) g)

/-- A seed in the second hat layer gives a subgroup of the local two-core. -/
theorem orbitFactor_le_Q [Finite M] {geometry : Geometry R}
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    {v : Vertex R} (hv : Z R v ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8)) :
    orbitFactor p v ≤ Q R (alpha R) :=
  (orbitFactor_le_second p hv).trans
    ((hatW_le_radius R p.two_step_distances.1.le p.two_step_distances.2.1.le).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4
        (by rw [earlier.distance]; decide)))

/-- The common denominator is central in the second hat layer. -/
theorem denominator_centralizes_second {geometry : Geometry R}
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    hatV R (alpha R) (p.walk.getVert 6) ≤
      centralizer (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :
        Set (FreeAmalgam R)) := by
  have hball : V R (alpha R) ≤ centralizer (VBall R (alpha R) 4 : Set (FreeAmalgam R)) := by
    apply (PathCentrality.V_le_iff R rfl _).mpr
    intro v hv hd
    apply le_centralizer_iff.mpr
    have hshift : VBall R (alpha R) 4 ≤ VBall R v 6 :=
      Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le v (alpha R) 4 6
        (by rw [SimpleGraph.dist_comm]; omega)
    exact (hshift.trans (Escape.Propagation.RadiusFour.VBall_le_Q v hv 6
      (by rw [earlier.distance]; decide))).trans
        (le_centralizer_iff.mp
          (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes v hv)))
  exact (hatV_le_radius R p.two_step_distances.1.le).trans
    (hball.trans (centralizer_le
      (hatW_le_radius R p.two_step_distances.1.le p.two_step_distances.2.1.le)))

private theorem orbit_elementary {G : Type*} [Group G] (A P : Subgroup G)
    [IsElementaryAbelian 2 A] [IsMulCommutative (conjugatesIn A P)] :
    IsElementaryAbelian 2 (conjugatesIn A P) := by
  have he : conjugatesIn A P = closure (⋃ g : P, (rightConjugate A g : Set G)) :=
    iSup_eq_closure _
  have hc : IsMulCommutative (closure (⋃ g : P, (rightConjugate A g : Set G))) :=
    he ▸ (inferInstance : IsMulCommutative (conjugatesIn A P))
  let := hc
  rw [he]
  apply IsElementaryAbelian.closure_of_isMulCommutative
  intro x hx
  obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy, rfl⟩ := hg
  rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian y hy, map_one]

/-- Literal orbit abelianness supplies elementarity of the enlarged factor.
The abelianness premise is (4.5.4)(ii), owned by the orbit-geometry producer. -/
theorem orbitFactor_elementary [Finite M] {geometry : Geometry R}
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    {v : Vertex R} (hv : Z R v ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8))
    (hcolor : color R v = false)
    (hab : IsMulCommutative (conjugatesIn (Z R v) (stabilizer R (alpha R)))) :
    IsElementaryAbelian 2 (orbitFactor p v) := by
  let := Z_elementary_of_positive R geometry v hcolor (by
    rw [geometry.distance_constant v hcolor]
    change 0 < geometry.b R
    rw [earlier.distance]
    decide)
  let := hab
  let := orbit_elementary (Z R v) (stabilizer R (alpha R))
  let : IsElementaryAbelian 2 (hatV R (alpha R) (p.walk.getVert 6)) :=
    PathCentrality.localZSpan_elementary R (a := p.walk.getVert 6)
    (c := alpha R) rfl p.two_step_distances.1.le (by rw [earlier.distance]; decide)
  apply IsElementaryAbelian.sup_of_le_centralizer
  exact (denominator_centralizes_second earlier p).trans
    (centralizer_le (show conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) from
        le_sup_left.trans (orbitFactor_le_second p hv)))

/-- The actual d seed is in hat V_c. -/
theorem first_seed_le (p : Higher.SourcePath (alpha R)) :
    Z R (p.walk.getVert 8) ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8) :=
  PathCentrality.Z_le_localZSpan R _ _

/-- Delta's displayed three-factor product supplies its seed containment. -/
theorem delta_seed_le {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    Z R δ.vertex ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8) :=
  (le_sup_right.trans le_sup_left).trans δ.generation.ge

/-- Delta belongs to the M-color, by its actual G_c transporter. -/
theorem delta_color {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    color R δ.vertex = false := by
  rw [δ.vertex_eq, action_preserves_color]
  rfl

/-- The chosen delta is exactly two steps from c. -/
theorem delta_dist_middle {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    (cosetGraph R).dist δ.vertex (p.walk.getVert 6) = 2 := by
  have hfix : act R δ.transporter (p.walk.getVert 6) = p.walk.getVert 6 :=
    δ.transporter.property
  have hh := dist_act R (δ.transporter : FreeAmalgam R)
    (alpha R) (p.walk.getVert 6)
  rw [hfix, ← δ.vertex_eq] at hh
  exact hh.trans (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
