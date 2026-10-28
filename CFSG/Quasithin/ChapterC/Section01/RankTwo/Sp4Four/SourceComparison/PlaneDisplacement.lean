module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.Backward
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement

/-!
# The plane calculation at the original critical pair

The actual critical commutator lies in the endpoint seed, because the
starting seed normalizes that seed. The centralizing actors from source
(3.3) normalize the endpoint seed by adjacency. Consequently a marked
natural quotient in which the critical commutator covers a self-orthogonal
plane gives the original subgroup bound, with its full kernel retained.

This is the first symplectic calculation in MS93 (3.3), printed p.867.
It does not assert the source's subsequent complement or root comparison.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e t : Vertex R}

/-- The whole source commutator lies in the endpoint seed. -/
theorem critical_commutator_le_endpoint_seed (p : CriticalPath R geometry a e) :
    ⁅Z R a,Z R e⁆ ≤ Z R e := by
  apply le_normalizer_iff_commutator_le_right.mp
  exact (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a p.start_color)
    p.critical.1.le).trans (Z_normalized R e)

/-- The auxiliary source commutator contains the critical one at positive
critical distance, without using the binary recognition hypotheses. -/
theorem critical_commutator_le_auxiliary (p : CriticalPath R geometry a e)
    (hb : 0 < geometry.b R) :
    ⁅Z R a,Z R e⁆ ≤ ⁅X R a,X R e⁆ := by
  apply commutator_mono
  · exact geometry.omega_bound a p.start_color
      (by rw [geometry.distance_constant a p.start_color]; exact hb)
  · exact geometry.omega_bound e p.end_color
      (by rw [geometry.distance_constant e p.end_color]; exact hb)

/-- The literal centralizing actors normalize the endpoint seed. -/
theorem endpoint_seed_normalized_by_edge
    (het : Adjacent R e t) (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t) :
    Y ≤ normalizer (Z R e : Set (FreeAmalgam R)) := by
  intro y hy
  exact Z_normalized R e ((hY hy).2 e (adjacent_symm R het))

/-- The real symplectic action calculation applied to the original graph
quotient and centralizing actors. The displayed quotient and conjugation
formula retain the source maps, including any nonsplit central attachment. -/
theorem critical_plane_commutator_bound
    (p : CriticalPath R geometry a e) (het : Adjacent R e t)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t)
    (hc : Y ≤ centralizer ((⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) : Set _))
    {F : Type*} [Field F]
    (π : Z R e →* Multiplicative (Vector F)) (α : Y →* Sp F)
    (hact : ∀ (y : Y) (z : Z R e),
      π ⟨y.val*z.val*y.val⁻¹,
        (mem_normalizer_iff.mp (endpoint_seed_normalized_by_edge het Y hY y.property)
          z.val).mp z.property⟩ = Multiplicative.ofAdd (α y • (π z).toAdd))
    (W : Submodule F (Vector F)) (hW : (form F).orthogonal W = W)
    (hcover : ∀ w ∈ W, ∃ d : (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)),
      (π ⟨d.val,critical_commutator_le_endpoint_seed p d.property⟩).toAdd = w) :
    ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔ π.ker.map (Z R e).subtype := by
  exact commutator_le_plane_sup_kernel (Z R e) Y (⁅Z R a,Z R e⁆)
    (critical_commutator_le_endpoint_seed p) (endpoint_seed_normalized_by_edge het Y hY)
    π α hact W hW hcover hc

end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
