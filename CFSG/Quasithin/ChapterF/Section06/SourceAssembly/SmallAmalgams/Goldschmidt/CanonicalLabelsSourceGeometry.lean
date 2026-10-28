module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceCuts
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralBlockTwo
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralLabels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralTrackExclusion
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.PreferredTrack

/-!
# Centered labels from the original central intervals

The two-edge central block and the even fixed interval have the same midpoint:
the margin comparison bounds their difference by one, while parity makes that
difference even. Conjugating the central involution then constructs its actual
vertex labels and transfers the interval to the short balls and moved spheres.
The double-boundary commutator additionally shows that an even radius is two.
These are the geometric construction preceding the radius-one exclusion and
the local product and cyclic-center arguments in Goldschmidt (6.8).

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.3)--(6.8),
printed pp.397--400.
-/

@[expose] public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The original two-edge block is centered in the fixed interval. -/
theorem CubicTreeAction.centralInterval_centered_of_length_two
    (h : CubicTreeAction F) (hs : 5 ≤ s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (hw : d.centralRight - d.centralLeft = 2)
    (he : Even (d.fixedRight - d.fixedLeft)) :
    d.leftMargin = d.rightMargin ∧
      d.fixedLeft = d.centralLeft + 1 - (d.rightMargin + 1) ∧
      d.fixedRight = d.centralLeft + 1 + (d.rightMargin + 1) := by
  obtain ⟨hle, hge⟩ := h.central_margin_comparison hs hshort t hz hz d d
  obtain ⟨k, hk⟩ := he
  have hl := d.leftMargin_cast
  have hr := d.rightMargin_cast
  exact ⟨by omega, by omega, by omega⟩

/-- An even centered radius is two. This is the double-boundary part of
(6.8), before the separate exclusion of radius one. -/
theorem CubicTreeAction.centered_even_radius_eq_two
    (h : CubicTreeAction F) (hs : 5 ≤ s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (hw : d.centralRight - d.centralLeft = 2)
    (hm : d.leftMargin = d.rightMargin)
    (he : Even d.rightMargin) : d.rightMargin = 2 := by
  obtain ⟨n, hn⟩ := he
  let k : ℤ := n + 1
  let e := d.shift k
  have hl := d.leftMargin_cast
  have hr := d.rightMargin_cast
  have hbound := h.double_boundary_rightMargin_le_two hs hshort hC hA t
    hfinite hz (hz.shift k) d e (by
      change d.centralRight = d.fixedLeft + 2 * k
      dsimp only [k]
      omega) (by
      change d.fixedRight = d.centralLeft + 2 * k
      dsimp only [k]
      omega)
  have hpos := (h.centralInterval_chiefBounds_of_large_residual hC hA t hz d).2.2.1
  omega

/-- The actual source interval supplies all equivariant label, fixed-ball
and moved-sphere data. The only radius still requiring exclusion is one. -/
theorem CubicTreeAction.exists_centered_interval_labels
    (h : CubicTreeAction F) (hs : 5 ≤ s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hpreferred : AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) :
    ∃ (d : t.CentralInterval z) (c : ℤ) (r : ℕ) (f : RankTwo.Vertex F → G),
      d.centralLeft = c - 1 ∧ d.centralRight = c + 1 ∧
      d.fixedLeft = c - (r + 1) ∧ d.fixedRight = c + (r + 1) ∧
      (r = 1 ∨ r = 2 ∨ Odd r ∧ 3 ≤ r) ∧ f (t.vertex c) = z ∧
      (∀ w, w.type = (t.vertex c).type → orderOf (f w) = 2) ∧
      (∀ w, w.type = (t.vertex c).type → f w ∈ RankTwo.stabilizer F w ∧
        ∀ g ∈ RankTwo.stabilizer F w, Commute (f w) g) ∧
      (∀ (g : G) w, w.type = (t.vertex c).type → f (g • w) = g * f w * g⁻¹) ∧
      (∀ w, w.type = (t.vertex c).type → ∀ x,
        (RankTwo.graph F).dist w x ≤ r + 1 →
        (RankTwo.graph F).dist w x ≤ s → f w • x = x) ∧
      (∀ w, w.type = (t.vertex c).type → r + 2 ≤ s → ∀ x,
        (RankTwo.graph F).dist w x = r + 2 → f w • x ≠ x) := by
  obtain ⟨d⟩ := h.exists_centralInterval_of_not_mem_fixer t z hz (hfinite z hz)
  have hw := h.centralInterval_length_eq_two hs hshort p hp hn hC hA t
    hfinite hpreferred hz d
  have he := h.centralInterval_fixedLength_even hs hshort p hp hn hC hA t
    hfinite hpreferred hz d
  obtain ⟨hm, hL, hR⟩ := h.centralInterval_centered_of_length_two hs hshort t hz d hw he
  let c := d.centralLeft + 1
  let r := d.rightMargin
  have hc : ∀ g ∈ RankTwo.stabilizer F (t.vertex c), Commute z g :=
    h.centralizes_vertex_of_two_centralEdges (by omega) hshort t c
      (d.central (c - 1) (by dsimp [c]; omega) (by dsimp [c]; omega))
      (d.central c (by dsimp [c]; omega) (by dsimp [c]; omega))
  have hr : r = 1 ∨ r = 2 ∨ Odd r ∧ 3 ≤ r := by
    have hpos := (h.centralInterval_chiefBounds_of_large_residual hC hA t hz d).2.2.1
    rcases Nat.even_or_odd r with hr | hr
    · exact Or.inr (Or.inl (h.centered_even_radius_eq_two hs hshort hC hA t
        hfinite hz d hw hm hr))
    · by_cases hone : r = 1
      · exact Or.inl hone
      · exact Or.inr (Or.inr ⟨hr, by dsimp only [r]; obtain ⟨k, hk⟩ := hr; omega⟩)
  obtain ⟨f, hf, ho, hcentral, hconj, hball, hsphere⟩ :=
    h.exists_interval_orbit_labels hshort t hz d c r hL hR hc
  exact ⟨d, c, r, f, by dsimp only [c]; omega, by dsimp only [c]; omega,
    hL, hR, hr, hf, ho, hcentral, hconj, hball, hsphere⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
