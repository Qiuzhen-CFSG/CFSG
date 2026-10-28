module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic

/-!
# The finite extended-path output of MS93 (4.4.5)

Indices begin at zero, corresponding to source alpha-4. Critical windows
start at 0, 2, 4, 6 and 8. Nonnormalization is required at 2, 4, 6 and 8,
and turns at the even indices from 2 through b+2. The length is b+8.

The output record retains all these clauses and the path property. Its
window construction proves that the first three critical windows are regular
in the published sense. Constructing an inhabitant from the source inputs
remains an assembly obligation; this is not a proof of (4.4.5).

Source: Meierfrankenfeld--Stellmacher (1993), printed p.894, the three
displayed conditions at the start of (4.4.5).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}


/-- Color along any finite walk; shortestness is not needed for this parity fact. -/
theorem walk_vertex_color {a a' : Vertex R} (ha : color R a = false)
    (w : (cosetGraph R).Walk a a') {i : ℕ} (hi : i ≤ w.length) :
    color R (w.getVert i) = false ↔ Even i := by
  have h := walk_even_iff_color_eq R (w.take i)
  simpa only [SimpleGraph.Walk.take_length, inf_eq_left.mpr hi, ha, eq_comm] using h.symm

/-- Exact finite output required at the start of (4.4.5), printed p.894.
The walk starts at the source's a-4, so its index i is source offset i-4.
This record is an output specification; no existence is asserted here. -/
structure ExtendedPath (geometry : Geometry R) (a : Vertex R) where
  first : Vertex R
  last : Vertex R
  walk : (cosetGraph R).Walk first last
  start_color : color R first = false
  length_eq : walk.length = geometry.b R + 8
  isPath : walk.IsPath
  center_eq : walk.getVert 4 = a
  critical : ∀ i : ℕ, Even i → i ≤ 8 →
    (cosetGraph R).dist (walk.getVert i) (walk.getVert (i + geometry.b R)) = geometry.b R ∧
      ¬ Z R (walk.getVert i) ≤ Q R (walk.getVert (i + geometry.b R))
  nonnormalization : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 8 →
    ¬ Z R (walk.getVert (i + geometry.b R)) ≤ stabilizer R (walk.getVert i) ⊓
      normalizer (edgeCommutator R (walk.getVert i) (walk.getVert (i - 1)) : Set (FreeAmalgam R))
  turns : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ geometry.b R + 2 →
    ∃ g ∈ stabilizer R (walk.getVert i),
      Stellmacher.PushingUp.AmalgamGraph.act R g (walk.getVert (i + 2)) =
        walk.getVert (i - 2)

namespace ExtendedPath
variable {a : Vertex R}

noncomputable def window (e : ExtendedPath geometry a) (i : ℕ) (hi : Even i) (hi8 : i ≤ 8) :
    CriticalPath R geometry (e.walk.getVert i) (e.walk.getVert (i + geometry.b R)) := by
  have hlen : geometry.b R ≤ (e.walk.drop i).length := by
    rw [SimpleGraph.Walk.drop_length, e.length_eq]
    omega
  have htarget : (e.walk.drop i).getVert (geometry.b R) =
      e.walk.getVert (i + geometry.b R) := SimpleGraph.Walk.drop_getVert _ _ _
  let w := ((e.walk.drop i).take (geometry.b R)).copy rfl htarget
  have hw : w.length = geometry.b R := by
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length, inf_eq_left.mpr hlen]
  have hc : color R (e.walk.getVert i) = false :=
    (walk_vertex_color e.start_color e.walk (by rw [e.length_eq]; omega)).mpr hi
  have hp := e.critical i hi hi8
  exact ⟨hc, w, hw.trans hp.1.symm,
    ⟨hp.1.trans (geometry.distance_constant _ hc).symm, hp.2⟩⟩

theorem window_getVert (e : ExtendedPath geometry a) (i : ℕ) (hi : Even i) (hi8 : i ≤ 8)
    (j : ℕ) (hj : j ≤ geometry.b R) :
    (e.window i hi hi8).walk.getVert j = e.walk.getVert (i + j) := by
  simp only [window, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
    inf_eq_right.mpr hj, SimpleGraph.Walk.drop_getVert]

/-- The first three critical windows retain every turn required by (4.4.2).
In particular this applies to the central pair, at index four. -/
theorem window_regular (e : ExtendedPath geometry a) (i : ℕ) (hi : Even i) (hi4 : i ≤ 4) :
    HasTurnConjugators R (e.window i hi (by omega)) := by
  intro j hj hj₂ hjend
  have hlen := (e.window i hi (show i ≤ 8 by omega)).length_eq_b
  have hsum : Even (i + j) := hi.add hj
  obtain ⟨g, hg, ht⟩ := e.turns (i + j) hsum (by omega) (by omega)
  refine ⟨g, ?_, ?_⟩
  · rwa [e.window_getVert i hi (by omega) j (by omega)]
  · rw [e.window_getVert i hi (by omega) (j + 2) (by omega),
      e.window_getVert i hi (by omega) (j - 2) (by omega)]
    have hsub : i + (j - 2) = i + j - 2 := by omega
    rwa [← Nat.add_assoc, hsub]

end ExtendedPath

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
