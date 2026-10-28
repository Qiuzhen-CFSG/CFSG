module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked.Actor

/-!
# The neighboring marked quotient and its actual actor

The package at c = a+2 uses one local conjugation chart for the natural
U_c and the doubled-dual second quotient. Its actor is the literal image
of Q_a, has order four, and fixes the natural-coordinate plane U_c ∩ Z_t.
The constructor applies the transport and edge-plane results to the actual
vertices 5, 6, 8 and 10 of the common source path.

The marked section and the two earlier-source statements remain explicit:
the genuine section from `Higher.Sections`, the first-layer identity
(4.5.3)(i), and the cardinality (4.5.1)(v). Their source producers must
supply them in the final neighboring-action assembly. This module proves
no final displacement bound and uses no (4.5.5) conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), pp.881 and 896--899.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked
open DistanceFour.Linear NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Compatible coordinates and the genuine fixed-plane actor at the source neighbor. -/
structure Data (common : CommonFacts R source geometry)
    (p : Higher.SourcePath (alpha R)) (g : FreeAmalgam R) where
  localEquiv : M ≃* stabilizer R (p.walk.getVert 6)
  localEquiv_val : ∀ m, (localEquiv m : FreeAmalgam R) = g⁻¹ * embedM R m * g
  projection : stabilizer R (p.walk.getVert 6) →* S
  projection_eq : projection = common.natural.marking.toMonoidHom.comp
    (source.projection.comp localEquiv.symm.toMonoidHom)
  projection_onto : Function.Surjective projection
  projection_kernel : projection.ker =
    (Q R (p.walk.getVert 6)).subgroupOf (stabilizer R (p.walk.getVert 6))
  naturalEquiv : U R (p.walk.getVert 6) ≃* Multiplicative W
  natural_action : ∀ (q : stabilizer R (p.walk.getVert 6)) (x y : U R (p.walk.getVert 6)),
    (y : FreeAmalgam R) = (q : FreeAmalgam R) * x * (q : FreeAmalgam R)⁻¹ →
    (naturalEquiv y).toAdd = (projection q).val.mulVec (naturalEquiv x).toAdd
  quotient : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) →*
    Multiplicative (W × W)
  quotient_onto : Function.Surjective quotient
  quotient_kernel : quotient.ker =
    (hatV R (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
      (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))
  quotient_action : ∀ (q : stabilizer R (p.walk.getVert 6))
    (x y : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)),
    (y : FreeAmalgam R) = (q : FreeAmalgam R) * x * (q : FreeAmalgam R)⁻¹ →
    (quotient y).toAdd =
      (dual (projection q) (quotient x).toAdd.1, dual (projection q) (quotient x).toAdd.2)
  actor_card : Nat.card
    (((Q R (alpha R)).subgroupOf (stabilizer R (p.walk.getVert 6))).map projection) = 4
  plane : Submodule (ZMod 2) W
  plane_mem : ∀ v, v ∈ plane ↔ ∃ x : U R (p.walk.getVert 6),
    (x : FreeAmalgam R) ∈ Z R (p.walk.getVert 5) ∧ (naturalEquiv x).toAdd = v
  plane_card : Nat.card plane = 4
  actor_fixes_plane : ∀ k ∈
    (((Q R (alpha R)).subgroupOf (stabilizer R (p.walk.getVert 6))).map projection),
    ∀ v ∈ plane, k.val.mulVec v = v

/-- Construct the full package from the literal pulled section, the earlier
first-layer identity, and the earlier H-cardinality. -/
noncomputable def data [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (g : FreeAmalgam R) (hg : act R g (alpha R) = p.walk.getVert 6)
    (s : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) g⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hH : Nat.card (H R (alpha R)) = 4) : Data common p g := by
  have hc : color R (p.walk.getVert 6) = false :=
    (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 4) (by rw [p.length_eq]; decide))
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 5) (by rw [p.length_eq]; decide)))
  exact {
    localEquiv := localEquiv g hg
    localEquiv_val := localEquiv_val g hg
    projection := projection common g hg
    projection_eq := rfl
    projection_onto := projection_onto common g hg
    projection_kernel := projection_kernel common g hg
    naturalEquiv := naturalEquiv common g hg
    natural_action := natural_action common g hg
    quotient := pairQuotient s
    quotient_onto := pairQuotient_onto s
    quotient_kernel := pairQuotient_kernel s
    quotient_action := pairQuotient_action s hg
    actor_card := actor_card common g hg earlier rfl p.two_step_distances.1 hat hct hVa hH
    plane := plane common g hg (p.walk.getVert 5)
    plane_mem := mem_plane common g hg (p.walk.getVert 5)
    plane_card := plane_card common g hg earlier hc hct
    actor_fixes_plane := actor_fixes_plane common g hg rfl hc hat hct }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked
