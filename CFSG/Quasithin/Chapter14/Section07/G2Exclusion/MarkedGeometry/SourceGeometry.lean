module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models

/-!
# The source quotient geometry and its two graphs

The model realizations are transported to the actual source quotient. We
identify its bipartite incidence graph with the concrete octonion hexagon,
so the proved diameter and girth bounds transfer. Separately, the graph on
its singular point subgroups, adjacent when contained in a common geometric
line, is isomorphic to the point collinearity graph and has no four-cycle.
The distinction matters: this latter graph does have triangles on lines.

The final theorem applies the natural/Weyl construction to the existing
14.7.53 endpoint. It removes that endpoint's `QuotientGeometry` premise;
the module identification, marked subgroup images and line-family equations
remain explicit obligations of the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
14.7.55(7), printed p.1066, and Theorem 14.7.53, printed pp.1068–1069.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2 Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

variable {Q : Type*} [Group Q]

/-- The bipartite incidence graph on the actual line and point subgroups.
This graph is kept separate from the point collinearity graph below. -/
def realizedIncidence (geom : QuotientGeometry Q) :
    SimpleGraph (Set.range geom.line ⊕ Set.range geom.point) where
  Adj x y := match x, y with
    | .inl L, .inr P => P.val ≤ L.val
    | .inr P, .inl L => P.val ≤ L.val
    | _, _ => False
  symm := by constructor; intro x y; cases x <;> cases y <;> exact id
  loopless := by constructor; intro x; cases x <;> exact id

/-- The subgroup geometry is isomorphic to the proved octonion incidence
hexagon. This identifies both kinds of vertices and the actual inclusions. -/
def realizedIncidenceIso (geom : QuotientGeometry Q) :
    geometryGraph (F := ZMod 2) ≃g realizedIncidence geom where
  toEquiv := Equiv.sumCongr (Equiv.ofInjective geom.line geom.line.injective)
    (Equiv.ofInjective geom.point geom.point.injective)
  map_rel_iff' := by
    intro x y
    cases x with
    | inl L =>
      cases y with
      | inl M => exact Iff.rfl
      | inr p => exact (geom.incidence p L).symm
    | inr p =>
      cases y with
      | inl L => exact (geom.incidence p L).symm
      | inr q => exact Iff.rfl

/-- Girth at least twelve in the realized incidence graph, deduced from the
proved model metric rather than included in the source assumptions. -/
theorem realizedIncidence_girth (geom : QuotientGeometry Q)
    (P : Set.range geom.line ⊕ Set.range geom.point)
    (w : (realizedIncidence geom).Walk P P) (hw : w.IsCycle) : 12 ≤ w.length := by
  let e := (realizedIncidenceIso geom).symm
  have hc : (w.map e.toHom).IsCycle := hw.map e.injective
  have hn := geometryGraph_girth_bound (e P) (w.map e.toHom) hc
  simpa only [SimpleGraph.Walk.length_map] using hn

/-- Diameter at most six, with paths on the actual point and line subgroups. -/
theorem realizedIncidence_diameter (geom : QuotientGeometry Q)
    (x y : Set.range geom.line ⊕ Set.range geom.point) :
    ∃ w : (realizedIncidence geom).Walk x y, w.length ≤ 6 := by
  let e := realizedIncidenceIso geom
  obtain ⟨x,rfl⟩ := e.surjective x
  obtain ⟨y,rfl⟩ := e.surjective y
  obtain ⟨w,hw⟩ := geometryGraph_diameter_bound x y
  exact ⟨w.map e.toHom, by simpa only [SimpleGraph.Walk.length_map] using hw⟩

/-- The point collinearity graph on the actual order-two subgroups realizing
singular points. Vertices sharing a geometric line are adjacent. -/
def realizedCollinearity (geom : QuotientGeometry Q) :
    SimpleGraph (Set.range geom.point) where
  Adj P R := P ≠ R ∧ ∃ L, P.val ≤ geom.line L ∧ R.val ≤ geom.line L
  symm := ⟨fun _ _ ⟨h,L,hP,hR⟩ => ⟨h.symm,L,hR,hP⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The isomorphism uses the actual containment incidence, not an assumed
cycle prohibition. -/
def realizedCollinearityIso (geom : QuotientGeometry Q) :
    collinearityGraph (F := ZMod 2) ≃g realizedCollinearity geom where
  toEquiv := Equiv.ofInjective geom.point geom.point.injective
  map_rel_iff' := by
    intro p q
    change ((⟨geom.point p, _⟩ : Set.range geom.point) ≠ ⟨geom.point q, _⟩ ∧
      ∃ L, geom.point p ≤ geom.line L ∧ geom.point q ≤ geom.line L) ↔ _
    constructor
    · rintro ⟨hpq,L,hp,hq⟩
      exact ⟨fun h => hpq (by subst q; rfl), L,
        (geom.incidence p L).mpr hp, (geom.incidence q L).mpr hq⟩
    · rintro ⟨hpq,L,hp,hq⟩
      exact ⟨fun h => hpq (geom.point.injective (congrArg Subtype.val h)), L,
        (geom.incidence p L).mp hp, (geom.incidence q L).mp hq⟩

/-- Lemma 14.7.55(7)'s four-cycle prohibition on the literal subgroup
realization of either module. Triangles contained in one line are allowed. -/
theorem realizedCollinearity_no_four_cycle (geom : QuotientGeometry Q)
    (P : Set.range geom.point) (w : (realizedCollinearity geom).Walk P P)
    (hw : w.IsCycle) : w.length ≠ 4 := by
  let e := (realizedCollinearityIso geom).symm
  have hc : (w.map e.toHom).IsCycle := hw.map e.injective
  have hn := binary_collinearity_no_four_cycle (e P) (w.map e.toHom) hc
  simpa only [SimpleGraph.Walk.length_map] using hn

/-- The two actual module identifications allowed by 14.7.54, in multiplicative
notation for use with the source quotient. An equivariant identification
supplies one of these underlying equivalences. -/
def ModuleIdentification (Q : Type*) [Group Q] :=
  (Multiplicative (TraceZero (ZMod 2)) ≃* Q) ⊕
    (Multiplicative (Space (ZMod 2)) ≃* Q)

/-- Construct the source geometry from the given actual module identification. -/
def ModuleIdentification.geometry (e : ModuleIdentification Q) : QuotientGeometry Q :=
  match e with
  | .inl e => transportGeometry weylMap.geometry e
  | .inr e => transportGeometry naturalMap.geometry e

/-- The no-four-cycle source assertion for the actual quotient `U/V₁`, with
only the module identification left to the 14.7.54 assembly owner. -/
theorem identified_quotient_no_four_cycle (N : Subgroup Q) [N.Normal]
    (e : ModuleIdentification (Q ⧸ N)) (P : Set.range e.geometry.point)
    (w : (realizedCollinearity e.geometry).Walk P P) (hw : w.IsCycle) :
    w.length ≠ 4 := realizedCollinearity_no_four_cycle e.geometry P w hw

/-- Actual application to the endpoint of 14.7.53. The point/line incidence
witness is now constructed from the natural/Weyl identification. The marked
source subgroups and line-family identities (c), (c′) remain explicit. -/
theorem false_of_identified_quotient_line_families
    (N : Subgroup Q) [N.Normal] (e : ModuleIdentification (Q ⧸ N))
    (U A P Z R S : Subgroup Q)
    (hPA : ¬ P ≤ A) (hZU : ¬ Z ≤ U) (hZA : Z ≤ A)
    (hRU : R ≤ U) (hRA : R ≤ A) (hSU : S ≤ U) (hSA : S ≤ A)
    (hNR : N ≤ R) (hNS : N ≤ S) (hRS : R ≠ S)
    (p z r s : SingularPoints (ZMod 2))
    (hp : e.geometry.point p = P.map (QuotientGroup.mk' N))
    (hz : e.geometry.point z = Z.map (QuotientGroup.mk' N))
    (hr : e.geometry.point r = R.map (QuotientGroup.mk' N))
    (hs : e.geometry.point s = S.map (QuotientGroup.mk' N))
    (Lpr Lps Lzr Lzs : ZeroProductLine (ZMod 2))
    (hLpr : e.geometry.line Lpr = (R ⊔ P).map (QuotientGroup.mk' N))
    (hLps : e.geometry.line Lps = (S ⊔ P).map (QuotientGroup.mk' N))
    (hLzr : e.geometry.line Lzr = (R ⊔ Z).map (QuotientGroup.mk' N))
    (hLzs : e.geometry.line Lzs = (S ⊔ Z).map (QuotientGroup.mk' N)) : False :=
  false_of_source_quotient_line_families N e.geometry U A P Z R S
    hPA hZU hZA hRU hRA hSU hSA hNR hNS hRS p z r s hp hz hr hs
    Lpr Lps Lzr Lzs hLpr hLps hLzr hLzs

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
