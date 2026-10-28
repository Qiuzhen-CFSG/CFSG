module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Neighbors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# The actual edge actor before centralizer selection

The contrary edge identity puts the displacement at every moving neighbor
in U_c, and the other neighbors lie in B_c by definition. Thus the earlier
source transfer (4.2)(i) puts the c-displacement in Z_t. It is consequently
fixed pointwise by Q_t. Its order four and the faithful natural action
identify the marked image of Q_t with the full pointwise plane fixer.

Only earlier source inputs are used. The index calculation imported from
Propagation.Edges is its conditional elementary action theorem; its edge
containment premise is proved here without LocalControl or b > 6.
This is a prerequisite for the generation display, not that display itself.

Source: Meierfrankenfeld--Stellmacher (1993), (4.2)(i), p.882, and the
display immediately before (4.3.2)(4), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

theorem edge_le_edge_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) :
    edgeDisplacement c t ≤ Z R t := by
  apply EdgeTransfer.edgeTransfer hb modules c t hc hct
  intro d hdt
  by_cases hmove : d ∈ movingNeighbors geometry c
  · rw [facts.edge_eq c t d hc hct hdt hmove]
    exact ((Initial.edge_le_natural source c t hc hct).trans (U_le_Z c)).trans
      (EdgeTransfer.Z_le_B hb c hc)
  have hdB : Z R d ≤ B R c (geometry.Z_normal c) := by
    by_cases he : c = d
    · subst d
      exact EdgeTransfer.Z_le_B hb c hc
    have hd : color R d = false := by
      have h₁ := adjacent_color_ne R hct
      have h₂ := adjacent_color_ne R hdt
      cases ht : color R t <;> cases hd : color R d <;> simp_all
    have hlow := (cosetGraph_connected R).one_lt_dist_of_ne_of_not_adj he (by
      intro h
      exact (adjacent_color_ne R ((cosetGraph_adj R _ _).mp h)) (hc.trans hd.symm))
    have hupp := (cosetGraph_connected R).dist_triangle (u := c) (v := t) (w := d)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hct),
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))] at hupp
    exact of_not_not (fun h => hmove ⟨by omega, h⟩)
  exact (le_normalizer_iff_commutator_le_left.mp
    ((show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (Z_normalized R d))).trans hdB

theorem edge_centralizes_kernel (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) :
    edgeDisplacement c t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
  have h := edge_le_edge_Z source hb modules facts hc hct
  rw [EdgeTransfer.edge_Z_eq_fixed hb modules c t hc hct] at h
  exact h.trans inf_le_right

open Propagation.Backward.Products.Selection.Choices (planeFixer planeStabilizer modelAction)
open Propagation.Backward.Products.Selection.Choices.FiniteGeometry

theorem edge_kernel_image (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (o : OppositeSectionAt c) :
    actorImage o (Q R t) = planeFixer (naturalImage o (edgeDisplacement c t)) := by
  let A := stabilizer R c
  let T := (Q R t).subgroupOf A
  let E := naturalImage o (edgeDisplacement c t)
  have hTA : Q R t ≤ A := fun _ hx => hx.2 c (adjacent_symm R hct)
  have hQindex := Propagation.edge_Q_index_of_card hb modules c t hc hct
    (edge_le_edge_Z source hb modules facts hc hct)
    (FirstPairing.StepThree.edge_card p (by omega) initial c t hc hct)
  have hcard : Nat.card (actorImage o (Q R t)) = 4 := by
    rw [actorImage, ← relIndex_ker, markedProjection_kernel, relIndex_subgroupOf hTA]
    exact hQindex
  have hle : actorImage o (Q R t) ≤ planeFixer E := by
    rintro _ ⟨g, hg, rfl⟩
    have hfix := (fixes_iff_centralizes o (edgeDisplacement c t)
      (Initial.edge_le_natural source c t hc hct) g).mpr
      (le_centralizer_iff.mp (edge_centralizes_kernel source hb modules facts hc hct) hg)
    intro v hv
    exact Multiplicative.toAdd.injective (hfix v hv)
  apply eq_of_le_of_card_ge hle
  rw [planeFixer_card E (edge_image_card source p (by omega) initial hc hct o), hcard]


/-- Distinct displacement planes give the precise relative centralizer.
A vector in the first plane outside the second is fixed by the actual Q_t. -/
theorem centralizer_eq_of_distinct_edges (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t s : Vertex R} (hc : color R c = false)
    (hct : Adjacent R c t) (hcs : Adjacent R c s)
    (hne : edgeDisplacement c t ≠ edgeDisplacement c s) :
    Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c := by
  let := finite_stabilizer R c
  have hlocal := (Initial.edge_le_natural source c s hc hcs).trans
    ((U_le_Z c).trans (Z_le_stabilizer R c))
  let : Finite (edgeDisplacement c s) := Finite.of_injective
    (inclusion hlocal) (inclusion_injective _)
  have hnot : ¬ edgeDisplacement c t ≤ edgeDisplacement c s := by
    intro h
    apply hne
    apply eq_of_le_of_card_ge h
    rw [FirstPairing.StepThree.edge_card p (by omega) initial c t hc hct,
      FirstPairing.StepThree.edge_card p (by omega) initial c s hc hcs]
  obtain ⟨u, hu, hus⟩ := SetLike.not_le_iff_exists.mp hnot
  exact centralizer_eq_of_fixed_outside source modules initial p (by omega) hc hct hcs
    (Initial.edge_le_natural source c t hc hct hu)
    (edge_centralizes_kernel source hb modules facts hc hct hu) hus

/-- An eligible displacement is different from the plane fixed by Q_t. -/
theorem edges_distinct_of_centralizer_eq (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    {c t s : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (hs : Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c) :
    edgeDisplacement c t ≠ edgeDisplacement c s := by
  intro he
  have hTQ : Q R t ≤ Q R c := by
    rw [← hs]
    apply le_inf le_rfl
    rw [← he]
    exact le_centralizer_iff.mp (edge_centralizes_kernel source hb modules facts hc hct)
  apply EdgeTransfer.edge_commutator_ne_bot modules c t hc hct
  apply le_bot_iff.mp
  exact (commutator_mono le_rfl hTQ).trans (geometry.centralizes c hc).le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay
