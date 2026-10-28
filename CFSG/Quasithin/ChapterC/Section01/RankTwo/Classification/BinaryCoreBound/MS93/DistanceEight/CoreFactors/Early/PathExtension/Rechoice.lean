module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.PathExtension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels.Rechoice

/-!
# The actual relative-normalizer rechoice in MS93 (4.5.3)

The relative normalizer preserves the preceding Z-layer and the incident edge
Z-layer. A local turn therefore gives a new regular critical window beginning
at the conjugated seed. Uniqueness of the middle vertex in the amalgam tree
preserves its first edge inequality. The window-extension theorem then embeds
that exact window in a full source path, retaining the original distant kernel.

This constructs both orientations of RechoicesOnPath and applies (4.5.1)(iii)
to prove the first D-containment. Neither the contrary hat identity nor a seed
containment is needed for this geometric step. Earlier is precisely the preceding
(4.4) source output; its separate producer remains responsible for those clauses.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), claim (1), p.897.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.PathExtension
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

open Orbit.Source Orbit.Source.HatIdentity Orbit.Source.HatIdentity.Preliminary
open Orbit.Source.HatIdentity.Preliminary.Kernels
open NormalizerTransfer

omit [Finite M] in
private theorem middle_unique (geometry : Geometry R) {a b c d : Vertex R}
    (hab : (cosetGraph R).dist a b = 2)
    (hac : Adjacent R a c) (hbc : Adjacent R b c)
    (had : Adjacent R a d) (hbd : Adjacent R b d) : c = d := by
  let w₁ : (cosetGraph R).Walk a b :=
    .cons ((cosetGraph_adj R _ _).mpr hac) (.cons ((cosetGraph_adj R _ _).mpr hbc).symm .nil)
  let w₂ : (cosetGraph R).Walk a b :=
    .cons ((cosetGraph_adj R _ _).mpr had) (.cons ((cosetGraph_adj R _ _).mpr hbd).symm .nil)
  have h₁ : w₁.IsPath := w₁.isPath_of_length_eq_dist (by simpa [w₁] using hab.symm)
  have h₂ : w₂.IsPath := w₂.isPath_of_length_eq_dist (by simpa [w₂] using hab.symm)
  have he : w₁ = w₂ := Subtype.mk.inj
    ((geometry.tree.isAcyclic.subsingleton_path a b).elim ⟨w₁, h₁⟩ ⟨w₂, h₂⟩)
  exact congrArg (fun w : (cosetGraph R).Walk a b => w.getVert 1) he

/-- The actual relative-normalizer conjugate lies on a complete source window.
No containment of that conjugate in the target kernel is assumed. -/
theorem forward_rechosenWindow (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    {g : FreeAmalgam R}
    (hg : g ∈ relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i - 1))) :
    Nonempty (RechosenWindow R (p.walk.getVert (i - 2)) (p.walk.getVert (i + 4)) g) := by
  obtain ⟨hcrit, hne, k, hk, hturn⟩ := forward_rechoice_geometry common earlier p hi hi4 hi6 hg
  let q := sourceWindow earlier.distance p i hi hi6
  have hl : q.walk.length = 8 := q.length_eq_b.trans earlier.distance
  have hq (j : ℕ) (hj : j ≤ 8) : q.walk.getVert j = p.walk.getVert (i + j) :=
    sourceWindow_getVert earlier.distance p i hi hi6 j hj
  have hn : ¬ (Z R (q.walk.getVert 2)).map (MulAut.conj k⁻¹).toMonoidHom ≤
      Q R (q.walk.getVert (q.walk.length - 2)) := by
    rw [← Z_act, hq 2 (by decide), hturn, hl, hq 6 (by decide)]
    exact hcrit.2
  let v := q.conjugateShift (by rw [earlier.distance]; decide) k hk hn
  have hvlen : v.walk.length = 8 := v.length_eq_b.trans earlier.distance
  have hv (j : ℕ) (hj : j ≤ 6) : v.walk.getVert (j + 2) = p.walk.getVert (i + j) := by
    change (q.conjugateShift (by rw [earlier.distance]; decide) k hk hn).walk.getVert (j + 2) = _
    unfold PathCentrality.CriticalPath.conjugateShift
    exact (q.prepend_two_overlap _ _ _ _ _ (by rw [hl]; exact hj)).trans (hq j (by omega))
  have hv0 : v.walk.getVert 0 = act R g (p.walk.getVert (i - 2)) := by
    rw [SimpleGraph.Walk.getVert_zero]
    rw [hq 2 (by decide), hturn]
  have hmiddle : act R k (p.walk.getVert (i + 1)) = act R g (p.walk.getVert (i - 1)) := by
    have hfixk : act R k (p.walk.getVert i) = p.walk.getVert i := hk
    have hfixg : act R g (p.walk.getVert i) = p.walk.getVert i := hg.1
    have hminus : Adjacent R (p.walk.getVert i) (p.walk.getVert (i - 1)) :=
      adjacent_symm R (by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
          p.adjacent (i := i - 1) (by omega))
    have hbefore : Adjacent R (p.walk.getVert (i - 2)) (p.walk.getVert (i - 1)) := by
      simpa only [show i - 2 + 1 = i - 1 by omega] using p.adjacent (i := i - 2) (by omega)
    apply middle_unique (geometry := geometry) (a := p.walk.getVert i)
      (b := act R g (p.walk.getVert (i - 2)))
    · rw [← hfixg, dist_act, SimpleGraph.dist_comm,
        p.distance (geometry := geometry) (by omega) (by omega)]
      omega
    · simpa only [hfixk] using (adjacent_act_iff R k _ _).mpr (p.adjacent (i := i) (by omega))
    · rw [← hturn]
      exact (adjacent_act_iff R k _ _).mpr (adjacent_symm R
        (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega)))
    · simpa only [hfixg] using (adjacent_act_iff R g _ _).mpr hminus
    · exact (adjacent_act_iff R g _ _).mpr hbefore
  have hv1 : v.walk.getVert 1 = act R g (p.walk.getVert (i - 1)) := by
    have hkfix : act R k (p.walk.getVert i) = p.walk.getVert i := hk
    let z : (cosetGraph R).Walk (act R k (q.walk.getVert 2)) (p.walk.getVert i) :=
      (actWalk R k (q.walk.take 2).reverse).copy rfl hkfix
    have hz : z.length = 2 := by
      simp only [z, SimpleGraph.Walk.length_copy, actWalk_length,
        SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length, hl]
      decide
    change (z.append (q.walk.take (q.walk.length - 2))).getVert 1 = _
    rw [SimpleGraph.Walk.getVert_append, hz, if_pos (by decide : 1 < 2)]
    simp only [z, SimpleGraph.Walk.getVert_copy, actWalk_getVert,
      SimpleGraph.Walk.getVert_reverse, SimpleGraph.Walk.take_length, hl,
      SimpleGraph.Walk.take_getVert]
    change act R k (q.walk.getVert 1) = _
    rw [hq 1 (by decide)]
    exact hmiddle
  have hreg : HasTurnConjugators R v :=
    hasTurnConjugators_conjugateShift q (by rw [earlier.distance]; decide)
      (sourceWindow_regular earlier.distance p i hi hi6) k hk hn
  have hsep : ∀ j, Even j → 2 ≤ j → j + 2 ≤ v.walk.length →
      Z R (v.walk.getVert (j - 1)) ≠ Z R (v.walk.getVert (j + 1)) := by
    intro j hj hj2 hjend
    rw [hvlen] at hjend
    by_cases h2 : j = 2
    · subst j
      rw [hv1, show 2 + 1 = 1 + 2 by rfl, hv 1 (by decide)]
      exact hne
    · have hj4 : 4 ≤ j := by rw [Nat.even_iff] at hj; omega
      rw [show j - 1 = (j - 3) + 2 by omega, hv (j - 3) (by omega),
        show j + 1 = (j - 1) + 2 by omega, hv (j - 1) (by omega)]
      have he : Even (i + j - 2) := by rw [Nat.even_iff] at hi hj ⊢; omega
      simpa only [show i + j - 2 - 1 = i + (j - 3) by omega,
        show i + j - 2 + 1 = i + (j - 1) by omega] using
        p.edge_Z_ne (i + j - 2) he (by omega) (by omega)
  obtain ⟨c, ⟨w, hw⟩⟩ := sourcePath_preserving_window common earlier v hreg hsep
  exact ⟨{
    center := c
    path := w
    index := 2
    even_index := by decide
    lower := le_rfl
    upper := by decide
    seed_vertex := (hw 0 (by decide)).trans hv0
    kernel_vertex := (hw 6 (by decide)).trans (hv 4 (by decide)) }⟩


/-- The reversed source configurations retain the same target kernel. -/
theorem backward_rechosenWindow (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10)
    {g : FreeAmalgam R}
    (hg : g ∈ relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i + 1))) :
    Nonempty (RechosenWindow R (p.walk.getVert (i + 2)) (p.walk.getVert (i - 4)) g) := by
  obtain ⟨c, ⟨q, hq⟩⟩ := reverse_sourcePath common earlier p
  have hj : Even (14 - i) := by rw [Nat.even_iff] at hi ⊢; omega
  have hgj : g ∈ relativeNormalizer R (q.walk.getVert (14 - i))
      (q.walk.getVert (14 - i - 1)) := by
    rw [hq, hq, show 14 - (14 - i) = i by omega,
      show 14 - (14 - i - 1) = i + 1 by omega]
    exact hg
  have h := forward_rechosenWindow common earlier q hj (by omega) (by omega) hgj
  rw [hq, hq, show 14 - (14 - i - 2) = i + 2 by omega,
    show 14 - (14 - i + 4) = i - 4 by omega] at h
  exact h

/-- The path rechoices in both directions are constructed, rather than assumed.
The contrary and displacement hypotheses are unnecessary for this geometric step. -/
theorem rechoicesOnPath (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) :
    RechoicesOnPath R p where
  forward _ hi h4 h6 _ _ _ hg _ := forward_rechosenWindow common earlier p hi h4 h6 hg
  backward _ hi h8 h10 _ _ _ hg _ := backward_rechosenWindow common earlier p hi h8 h10 hg

/-- The first D-containment of (4.5.3) holds on the literal source path. -/
theorem forward_span_le_four (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 4)) :=
  span_le_four_of_rechoices common earlier
    (fun _ hg _ => forward_rechosenWindow common earlier p hi hi4 hi6 hg)

theorem backward_span_le_four (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 4)) :=
  span_le_four_of_rechoices common earlier
    (fun _ hg _ => backward_rechosenWindow common earlier p hi hi8 hi10 hg)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.PathExtension
