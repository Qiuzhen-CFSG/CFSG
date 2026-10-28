module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Neighbors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# Lifting the selected neighbors from the genuine dual moving quotient

The coordinates on Vcirc_c have kernel exactly U_c and intertwine the
actual conjugation action with the inverse-transpose matrix action.
An eligible neighbor exists by `exists_centralizing_neighbor`; its radius
group contains U_c. Thus surjectivity of the selected span on Vcirc_c/U_c
lifts to containment of Vcirc_c. The radius decomposition then recovers
all of V_c, including the part outside Vcirc_c.

The image-surjectivity premise remains explicit. This module does not prove
the local neighbor-generation identity before MS93 (4.3.2)(4).
Source: Meierfrankenfeld--Stellmacher (1993), printed p.884.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

noncomputable def movingCoordinates {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) : Vcirc R c →* Space :=
  o.dual.coordinates.comp (subgroupOfEquivOfLe hC).symm.toMonoidHom

theorem movingCoordinates_surjective {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) : Function.Surjective (movingCoordinates o hC) :=
  o.dual.surjective.comp (subgroupOfEquivOfLe hC).symm.surjective

theorem movingCoordinates_kernel {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) :
    (movingCoordinates o hC).ker = (U R c).subgroupOf (Vcirc R c) := by
  ext x
  change o.dual.coordinates ((subgroupOfEquivOfLe hC).symm x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, o.dual.kernel]
  rfl

theorem movingCoordinates_conjugation {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c)
    (g : stabilizer R c) (u v : Vcirc R c)
    (hv : (v : FreeAmalgam R) = g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    (movingCoordinates o hC v).toAdd =
      ((markedProjection o g)⁻¹.val).transpose.mulVec (movingCoordinates o hC u).toAdd := by
  exact o.dual.action g (mem_top g) _ _ (Subtype.ext hv)

noncomputable def selectedMovingImage {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) (t : Vertex R) : Subgroup Space :=
  ((centralizingNeighborSpan c t).subgroupOf (Vcirc R c)).map (movingCoordinates o hC)

theorem neighbor_le_span {c t s : Vertex R} (hcs : Adjacent R c s)
    (hs : Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c) :
    V R s ≤ centralizingNeighborSpan c t :=
  le_iSup_of_le s (le_iSup_of_le hcs (le_iSup_of_le hs le_rfl))

theorem natural_le_span {c t s : Vertex R} (hcs : Adjacent R c s)
    (hs : Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c) :
    U R c ≤ centralizingNeighborSpan c t := by
  apply (U_le_Z c).trans
  apply le_trans _ (neighbor_le_span hcs hs)
  exact le_iSup_of_le c (le_iSup_of_le
    (show (cosetGraph R).dist c s ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcs)).le.trans (by decide)) le_rfl)

theorem moving_le_span_of_image_eq_top {c t s : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) (hcs : Adjacent R c s)
    (hs : Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c)
    (himage : selectedMovingImage o hC t = ⊤) :
    Vcirc R c ≤ centralizingNeighborSpan c t := by
  have hker : (movingCoordinates o hC).ker ≤
      (centralizingNeighborSpan c t).subgroupOf (Vcirc R c) := by
    rw [movingCoordinates_kernel]
    exact fun _ hx => natural_le_span hcs hs hx
  have heq := congrArg (Subgroup.comap (movingCoordinates o hC)) himage
  change (((centralizingNeighborSpan c t).subgroupOf (Vcirc R c)).map
    (movingCoordinates o hC)).comap (movingCoordinates o hC) = _ at heq
  rw [comap_map_eq_self hker, comap_top] at heq
  intro x hx
  exact show (⟨x, hx⟩ : Vcirc R c) ∈ (centralizingNeighborSpan c t).subgroupOf (Vcirc R c) from
    heq.symm ▸ mem_top _

variable [Finite M]

theorem le_span_of_moving_image (source : LocalSource L R)
    {c t s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s)
    (o : OppositeSectionAt c) (hC : Vcirc R c ≤ stabilizer R c)
    (hs : Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c)
    (himage : selectedMovingImage o hC t = ⊤) :
    V R c ≤ centralizingNeighborSpan c t := by
  rw [Initial.Consequences.radius_eq_moving_sup_edge source hc hcs]
  exact sup_le (moving_le_span_of_image_eq_top o hC hcs hs himage) (neighbor_le_span hcs hs)

/-- Exact reduction of local generation to the image in the marked dual
three-space. The image condition still requires a proof from the source. -/
theorem le_span_iff_moving_image (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (o : OppositeSectionAt c) (hC : Vcirc R c ≤ stabilizer R c) :
    V R c ≤ centralizingNeighborSpan c t ↔ selectedMovingImage o hC t = ⊤ := by
  constructor
  · intro h
    have heq : (centralizingNeighborSpan c t).subgroupOf (Vcirc R c) = ⊤ := by
      apply top_unique
      intro x _
      exact h (Vcirc_le_V c x.property)
    rw [selectedMovingImage, heq, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (movingCoordinates_surjective o hC)
  · intro h
    obtain ⟨s, hcs, hs⟩ := exists_centralizing_neighbor source hb modules initial facts p hc hct
    exact le_span_of_moving_image source hc hcs o hC hs h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
