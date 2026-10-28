module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.FixedPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.RadiusCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Generation.PlaneNormalizer

/-!
# The source neighbor-generation display

The earlier edge transfer makes Q_t fix its natural displacement plane.
Every different displacement plane is therefore eligible for the relative
centralizer condition. Choose actual nonfixed vectors in V_t and an eligible
V_s. Their compatible full-radius covectors are nonzero and distinct, with
the corresponding displacement planes as their annihilators.

Lift the stabilizer of the first covector through the actual local residual.
Each conjugate of the second vector belongs to an actual eligible neighbor.
Its quotient by the original vector is a commutator in both the selected
span and Vcirc. These commutators cancel the entire component outside Vcirc;
the six-point orbit differences generate the full dual three-space. The
exact kernel Vcirc ∩ B = U lifts this to Vcirc, and the radius decomposition
with the original eligible neighbor recovers all of V.

The proof uses only LocalSource, b > 2, ModuleFacts, the supplied initial
facts, and ContraryLocalFacts. It neither requires individual native lifts
nor invokes b > 6 or later local control. The imported plane-normalizer
helpers concern only natural-coordinate injectivity and conjugation.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the display immediately before (4.3.2)(4), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay
open LocalProducts.StepSix.PlaneNormalizer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

private theorem residual_marked_surjective (source : LocalSource L R)
    {c : Vertex R} (hc : color R c = false) (o : OppositeSectionAt c) (g : SL) :
    ∃ l : stabilizer R c, (l : FreeAmalgam R) ∈ Ltilde R c ∧ markedProjection o l = g := by
  have hQ : Q R c ≤ stabilizer R c := fun _ hx => hx.1
  have hgen : (Ltilde R c).subgroupOf (stabilizer R c) ⊔
      (Q R c).subgroupOf (stabilizer R c) = ⊤ := by
    rw [← subgroupOf_sup (Ltilde_le_stabilizer c) hQ, source.local_generation c hc,
      subgroupOf_self]
  have hmap : ((Q R c).subgroupOf (stabilizer R c)).map (markedProjection o) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, markedProjection_kernel]
  have hm := congrArg (Subgroup.map (markedProjection o)) hgen
  rw [Subgroup.map_sup, hmap, sup_bot_eq, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (o.naturalU.marking.surjective.comp o.surjective)] at hm
  exact mem_map.mp (hm.symm ▸ mem_top g)

/-- The source display, using differences of actual neighboring elements.
The residual lifts cancel every component outside Vcirc before taking images. -/
theorem le_span (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    V R c ≤ centralizingNeighborSpan c t := by
  obtain ⟨q, hqc⟩ := Initial.Consequences.counterexample_at_start p c hc
  obtain ⟨iq⟩ := initial q
  have sectionAt : NaturalSectionAt c (V R c) (Z R c) := by
    simpa only [hqc] using iq.natural_section
  obtain ⟨o⟩ := facts.opposite c hc
  let f := radiusCoordinates source hb hc sectionAt o
  obtain ⟨xt, hxt, hdt, het⟩ := exists_neighbor_coordinate source hb modules initial facts p
    hc hct sectionAt o
  obtain ⟨s, hcs, hs⟩ := exists_centralizing_neighbor source hb modules initial facts p hc hct
  obtain ⟨x, hx, hv, hes⟩ := exists_neighbor_coordinate source hb modules initial facts p
    hc hcs sectionAt o
  let d := f xt
  let v := f x
  have hdv : d ≠ v := by
    intro he
    have heimage : naturalImage o (edgeDisplacement c t) = naturalImage o (edgeDisplacement c s) :=
      het.trans ((congrArg Model.annihilator he).trans hes.symm)
    exact edges_distinct_of_centralizer_eq source hb modules facts hc hct hs
      (naturalImage_injective o (Initial.edge_le_natural source c t hc hct)
        (Initial.edge_le_natural source c s hc hcs) heimage)
  let K := centralizingNeighborSpan c t
  let J := ((K ⊓ Vcirc R c).subgroupOf (V R c)).map f
  have hJ : J = ⊤ := by
    apply Model.differences_generate d v hdt hv hdv J
    intro g hgd
    obtain ⟨l, hlL, hlg⟩ := residual_marked_surjective source hc o g
    let s' := act R (l : FreeAmalgam R)⁻¹ s
    have hlc : act R (l : FreeAmalgam R)⁻¹ c = c := (stabilizer R c).inv_mem l.property
    have hcs' : Adjacent R c s' := by
      simpa only [hlc] using (adjacent_act_iff R (l : FreeAmalgam R)⁻¹ c s).mpr hcs
    have heconj : edgeDisplacement c s' =
        (edgeDisplacement c s).map (MulAut.conj (l : FreeAmalgam R)).toMonoidHom := by
      simpa only [hlc, inv_inv] using FirstPairing.edgeDisplacement_act
        (l : FreeAmalgam R)⁻¹ c s
    have heimage : naturalImage o (edgeDisplacement c s') =
        Model.annihilator (Model.dualAction g v) := by
      rw [heconj, naturalImage_conjugate o l _ (Initial.edge_le_natural source c s hc hcs),
        hes, Model.annihilator_move, hlg]
    have hne : edgeDisplacement c t ≠ edgeDisplacement c s' := by
      intro he
      have hcoord : d = Model.dualAction g v :=
        Model.annihilator_injective (het.symm.trans ((congrArg (naturalImage o) he).trans heimage))
      exact hdv ((Model.dualAction g).injective (hgd.trans hcoord))
    have hs' := centralizer_eq_of_distinct_edges source hb modules initial facts p hc hct hcs' hne
    let y : V R c := ⟨l * (x : FreeAmalgam R) * (l : FreeAmalgam R)⁻¹,
      le_normalizer_iff.mp (V_normalized c) l l.property x x.property⟩
    have hy : (y : FreeAmalgam R) ∈ V R s' := by
      rw [V_act]
      exact ⟨x, hx, by simp only [inv_inv]; rfl⟩
    have hyK : (y : FreeAmalgam R) ∈ K := neighbor_le_span hcs' hs' hy
    have hxK : (x : FreeAmalgam R) ∈ K := neighbor_le_span hcs hs hx
    have hzC : ((y * x⁻¹ : V R c) : FreeAmalgam R) ∈ Vcirc R c := by
      change ⁅(l : FreeAmalgam R), (x : FreeAmalgam R)⁆ ∈ ⁅V R c, Ltilde R c⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hlL x.property
    have hz : y * x⁻¹ ∈ (K ⊓ Vcirc R c).subgroupOf (V R c) :=
      ⟨K.mul_mem hyK (K.inv_mem hxK), hzC⟩
    have hcoord : f (y * x⁻¹) = Model.dualAction g v * v⁻¹ := by
      rw [map_mul, map_inv, radiusCoordinates_conjugation source hb hc sectionAt o l x y rfl,
        hlg]
    exact hcoord ▸ mem_map_of_mem f hz
  have hC : Vcirc R c ≤ K := moving_le_of_radius_image source hb hc sectionAt o K
    (natural_le_span hcs hs) hJ
  rw [Initial.Consequences.radius_eq_moving_sup_edge source hc hcs]
  exact sup_le hC (neighbor_le_span hcs hs)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The exact predecessor instance needed by the source centralizer-path assembly. -/
theorem local_neighbor_generation (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (_transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (_bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {t : Vertex R} (ht : Before p.a p.a' t 3) :
    V R p.c ≤ centralizingNeighborSpan p.c t := by
  exact SourceDisplay.le_span source hb modules initial facts p p.before_color
    (adjacent_symm R (ht.adjacent (geometry := geometry) p.before))

/-- The full source identity, retaining the actual relative centralizers. -/
theorem source_neighbor_generation (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    V R c = centralizingNeighborSpan c t :=
  le_antisymm (SourceDisplay.le_span source hb modules initial facts p hc hct)
    (centralizingNeighborSpan_le hc)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
