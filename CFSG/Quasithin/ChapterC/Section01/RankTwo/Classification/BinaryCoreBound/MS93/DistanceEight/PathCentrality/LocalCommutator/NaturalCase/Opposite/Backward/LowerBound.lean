module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Backward.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans

/-!
# Backward displacement from endpoint-preserving reselection

Conjugate the selected backward pair back to the original natural frame.
Its far endpoint is prescribed, and its local orbit escapes that endpoint's
kernel. A cover of the orbit by good conjugates and the incident radius
selects a good conjugate which still escapes: the radius lies in the far
kernel by critical minimality. This gives a genuine SelectedPath with the
original center and the prescribed endpoint, retaining every selection field.

Apply the supplied forward family to this new selection, then transport its
order-four lower bound back by the backward conjugator. The original edge
upper bound identifies the literal backward intersection with the edge.

The final assembly supplies the good-conjugate cover from
Selection.Paths.LocalSpans, using the selected path's original frame, moving
element and edge data. Thus the backward lower bound and its edge-identity
consumer retain only the common source facts, b > 4 and the supplied forward
family; no additional selection or cover premise remains.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891,
the good-conjugate selection and the final “as above” lower bound.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

namespace SelectedPath
variable (s : SelectedPath R geometry a c)

/-- The selected configuration already contains all of the local edge data. -/
def edgeData (hb : 2 ≤ geometry.b R) : Selection.EdgeData s.start s.center where
  neighbor := s.first
  adjacent_start := s.start_adjacent_first hb
  adjacent_center := adjacent_symm R (s.first_adjacent_center hb)
  element := s.element
  element_mem := s.element_mem
  moving := s.moving
  displacement := s.displacement
  edge_eq := s.edge_eq
  kernel_product := s.kernel_product

/-- This is the noncontainment input required by the local cover producer. -/
theorem displacement_not_le_fixed :
    ¬ ⁅Z R s.start, Q R s.center⁆ ≤ fixedCore R s.center := by
  intro h
  exact s.moving ((commutator_mono (zpowers_le.mpr s.element_mem) le_rfl).trans h)

private theorem selection_with_endpoints
    (hb : 2 ≤ geometry.b R)
    (p : Selection.PathPlacement geometry s.start s.center s.first) :
    ∃ t : SelectedPath R geometry s.start s.center,
      t.center = s.center ∧ t.endpoint = p.endpoint := by
  let e := s.edgeData hb
  have hcenter : act R p.conjugator s.center = p.path.walk.getVert 2 :=
    p.local_conjugator.trans p.center_eq.symm
  obtain ⟨f', hop'⟩ : ∃ f' : FrameAt p.start (p.path.walk.getVert 2),
      ¬ f'.SameOrientation := by
    rw [p.center_eq, ← p.start_image]
    obtain ⟨f', _, _, _, hop'⟩ :=
      Selection.frame_of_local_conjugator s.frame s.opposite p.local_conjugator
    exact ⟨f', hop'⟩
  have hedge : (edgeCommutator R s.start s.first).map
      (MulAut.conj p.conjugator⁻¹).toMonoidHom =
      edgeCommutator R p.start (p.path.walk.getVert 1) := by
    calc
      _ = edgeCommutator R (act R p.conjugator s.start)
          (act R p.conjugator s.first) := by
        simp only [edgeCommutator, Z_act, Q_act, map_commutator]
      _ = _ := congrArg₂ (edgeCommutator R) p.start_image p.first_image
  let t : SelectedPath R geometry s.start s.center := {
    start := p.start
    endpoint := p.endpoint
    path := p.path
    conjugator := p.conjugator
    start_image := p.start_image
    center_image := hcenter
    frame := f'
    opposite := hop'
    element := (MulAut.conj p.conjugator⁻¹) s.element
    element_mem := by
      rw [← p.start_image]
      exact (e.act p.conjugator).element_mem
    moving := by
      have h := (e.act p.conjugator).moving
      change ¬ ⁅zpowers ((MulAut.conj p.conjugator⁻¹) s.element),
        Q R (act R p.conjugator s.center)⁆ ≤
          fixedCore R (act R p.conjugator s.center) at h
      rwa [hcenter] at h
    displacement := by
      have h := (e.act p.conjugator).displacement
      change ⁅zpowers ((MulAut.conj p.conjugator⁻¹) s.element),
        Q R (act R p.conjugator s.center)⁆ =
          edgeCommutator R (act R p.conjugator s.start)
            (act R p.conjugator s.first) at h
      rwa [hcenter, p.start_image, p.first_image] at h
    edge_eq := by
      have h := (e.act p.conjugator).edge_eq
      change edgeCommutator R (act R p.conjugator s.start)
        (act R p.conjugator s.first) =
          edgeCommutator R (act R p.conjugator s.center)
            (act R p.conjugator s.first) at h
      rwa [hcenter, p.start_image, p.first_image] at h
    kernel_product := by
      have h := (e.act p.conjugator).kernel_product
      change Q R (act R p.conjugator s.start) ⊔ Q R (act R p.conjugator s.center) =
        Q R (act R p.conjugator s.first) ⊓ centralizer
          (edgeCommutator R (act R p.conjugator s.start)
            (act R p.conjugator s.first) : Set (FreeAmalgam R)) at h
      rwa [hcenter, p.start_image, p.first_image] at h
    centralizer_selection := by
      have h := p.centralizer_selection
      rw [hedge] at h
      exact h.trans (congrArg (Q R) p.center_eq.symm).le }
  exact ⟨t, p.center_eq, rfl⟩

/-- Reselect the start while preserving both the center and the specified
far endpoint. The good cover, rather than mere orbit escape, provides the
third-vertex centralizer selection. -/
theorem reselection_of_cover
    (hb : 4 < geometry.b R) (e : Vertex R)
    (hd : (cosetGraph R).dist s.center e + 2 = geometry.b R)
    (hout : ¬ localZSpan R s.start s.center ≤ Q R e)
    (cover : ∀ u : Vertex R, Adjacent R s.center u →
      localZSpan R s.start s.center ≤
        Selection.goodConjugateSpan s.start s.center s.first u ⊔ V R u) :
    ∃ t : SelectedPath R geometry s.start s.center,
      t.center = s.center ∧ t.endpoint = e := by
  classical
  obtain ⟨tail, htail⟩ :=
    (cosetGraph_connected R).exists_walk_length_eq_dist s.center e
  have hlen : tail.length + 2 = geometry.b R := by rwa [htail]
  have hcu : Adjacent R s.center (tail.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (tail.adj_getVert_succ (i := 0) (by omega))
  have hremaining : (cosetGraph R).dist (tail.getVert 1) e = tail.length - 1 := by
    have h := SimpleGraph.length_eq_dist_of_subwalk htail (tail.isSubwalk_drop 1)
    simpa only [SimpleGraph.Walk.drop_length] using h.symm
  have hV : V R (tail.getVert 1) ≤ Q R e :=
    Selection.incident_radius_le_kernel (s.center_color (by omega)) hcu
      (by rw [hremaining]; omega)
  obtain ⟨g, hgood, hcrit⟩ : ∃ g : stabilizer R s.center,
      Selection.GoodConjugate s.start s.center s.first (tail.getVert 1) g ∧
      ¬ Z R (act R g s.start) ≤ Q R e := by
    by_contra! h
    apply hout
    apply (cover _ hcu).trans
    exact sup_le (iSup_le fun g => iSup_le fun hg => h g hg) hV
  let p := Selection.pathPlacementOfConjugate s.path.start_color
    (s.edgeData (by omega)).toMovingSeed tail hlen g hcrit hgood
  obtain ⟨t, ht, he⟩ := s.selection_with_endpoints (by omega) p
  exact ⟨t, ht, he⟩

variable [Finite M]

/-- Apply the forward calculation to a true reselection at the conjugate
backward endpoint and transport the actual intersection back. Only the
independently owned good-conjugate cover remains to be supplied. -/
theorem backward_displacement_card_lower_of_cover
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (cover : ∀ u : Vertex R, Adjacent R s.center u →
      localZSpan R s.start s.center ≤
        Selection.goodConjugateSpan s.start s.center s.first u ⊔ V R u) :
    4 ≤ Nat.card (⁅Z R s.start, V R s.predecessor⁆ ⊓
      Z R s.predecessor : Subgroup (FreeAmalgam R)) := by
  obtain ⟨w⟩ := s.backwardChoice_nonempty common hb (forward s).moving_le_span
  let e := act R w.conjugator⁻¹ s.predecessor
  have he : act R w.conjugator e = s.predecessor := by
    simp only [e, ← act_mul, inv_mul_cancel, act_one]
  have hd : (cosetGraph R).dist s.center e + 2 = geometry.b R := by
    have h := dist_act R w.conjugator s.center e
    rw [w.center_image, he] at h
    rw [← h, s.path.dist_start (Nat.sub_le _ _), s.path.length_eq_b]
    omega
  have hout : ¬ localZSpan R s.start s.center ≤ Q R e := by
    intro h
    have hz := (Z_le_localZSpan R s.start s.center).trans h
    have hm := map_mono (f := (MulAut.conj w.conjugator⁻¹).toMonoidHom) hz
    rw [← Z_act, ← Q_act, w.start_image, he] at hm
    exact w.noncontainment hm
  obtain ⟨t, ht, hte⟩ := s.reselection_of_cover hb e hd hout cover
  have hlow := (forward t).displacement_card_lower t
  rw [ht, hte] at hlow
  let K := ⁅Z R s.center, V R e⁆ ⊓ Z R e
  have hmap : K.map (MulAut.conj w.conjugator⁻¹).toMonoidHom =
      ⁅Z R s.start, V R s.predecessor⁆ ⊓ Z R s.predecessor := by
    dsimp only [K]
    rw [map_inf _ _ _ (MulAut.conj w.conjugator⁻¹).injective,
      map_commutator, ← Z_act, ← V_act, ← Z_act, w.center_image, he]
  have hcard : Nat.card (⁅Z R s.start, V R s.predecessor⁆ ⊓
      Z R s.predecessor : Subgroup (FreeAmalgam R)) = Nat.card K := by
    rw [← hmap]
    exact card_map_of_injective (MulAut.conj w.conjugator⁻¹).injective
  exact hcard ▸ hlow

/-- Actual consumer: the proved lower bound fills the original edge, with
the source good-cover premise still explicit. -/
theorem backward_displacement_eq_of_cover
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (cover : ∀ u : Vertex R, Adjacent R s.center u →
      localZSpan R s.start s.center ≤
        Selection.goodConjugateSpan s.start s.center s.first u ⊔ V R u) :
    ⁅Z R s.start, V R s.predecessor⁆ ⊓ Z R s.predecessor = s.edge :=
  s.backward_displacement_eq_of_card_lower common hb
    (s.backward_displacement_card_lower_of_cover common hb forward cover)

/-- The backward order-four lower bound in MS93 (4.4.1)(1), with the
good-conjugate cover discharged on the original selected frame. -/
theorem backward_displacement_card_lower
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts) :
    4 ≤ Nat.card (⁅Z R s.start, V R s.predecessor⁆ ⊓
      Z R s.predecessor : Subgroup (FreeAmalgam R)) := by
  apply s.backward_displacement_card_lower_of_cover common hb forward
  intro u hcu
  exact Selection.localZSpan_le_goodConjugateSpan_sup_radius
    source common hb s.path.start_color (s.center_color (by omega))
    (s.center_distance (by omega)) s.displacement_not_le_fixed s.frame s.opposite
    (s.edgeData (by omega)) hcu

/-- The source lower bound fills the original edge and supplies the literal
displacement identity required by the backward-closing assembly. -/
theorem backward_displacement_eq
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts) :
    ⁅Z R s.start, V R s.predecessor⁆ ⊓ Z R s.predecessor = s.edge :=
  s.backward_displacement_eq_of_card_lower common hb
    (s.backward_displacement_card_lower common hb forward)

end SelectedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
