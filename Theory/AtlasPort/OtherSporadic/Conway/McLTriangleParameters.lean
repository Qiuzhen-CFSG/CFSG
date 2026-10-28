/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleParameters.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleShapes
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleParameterInjective

/-!
Explicit parameters for all four McLaughlin triangle shapes.
Golay octads and signed octads give a bijection onto the triangle slice;
coordinate injectivity and the shape classification prove the inverse laws.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleParameters.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev McLOctadCodes (v : Bit) := {c : golay // hammingNorm c.val = 8 ∧
  c.val co3MarkedCoordinate = v ∧ c.val co3BasePoint.val = v}

abbrev McLMixedOctads := {T // T ∈ octads.filter
  (fun T => co3MarkedCoordinate ∉ T ∧ co3BasePoint.val ∈ T)}

abbrev McLTriangleParameters : Fin 4 → Type
  | 0 => PUnit
  | 1 => McLOctadCodes 0
  | 2 => (c : McLOctadCodes 1) × {b : Omega // b ≠ co3MarkedCoordinate ∧
      b ≠ co3BasePoint.val ∧ c.val.val b = 1}
  | 3 => (T : McLMixedOctads) × {s : T.val → Bit // hammingNorm s = 2 ∧
      s ⟨co3BasePoint.val,(Finset.mem_filter.mp T.prop).2.2⟩ = 1}

def mclTriangleParameterVector : (t : Fin 4) → McLTriangleParameters t → leech
  | 0, _ => mclReferenceVector
  | 1, c => oddMinimumVector co3BasePoint.val c.val
  | 2, p => oddMinimumVector p.2.val p.1.val
  | 3, p => co3SignedOctadVector p.1.val (Finset.mem_filter.mp p.1.prop).1 p.2.val
      (by rw [bit_sum_eq_weight,p.2.prop.1]; decide)

theorem mcl_triangle_parameter_shape (t : Fin 4) (p : McLTriangleParameters t) :
    McLTriangleShape t (mclTriangleParameterVector t p) := by
  fin_cases t
  · rfl
  · exact ⟨p.val,p.prop.1,p.prop.2.1,p.prop.2.2,rfl⟩
  · exact ⟨p.2.val,p.1.val,p.2.prop.1,p.2.prop.2.1,p.1.prop.1,
      p.1.prop.2.1,p.1.prop.2.2,p.2.prop.2.2,rfl⟩
  · refine ⟨p.1.val,(Finset.mem_filter.mp p.1.prop).1,p.2.val,
      (Finset.mem_filter.mp p.1.prop).2.1,?_,
      ⟨(Finset.mem_filter.mp p.1.prop).2.2,p.2.prop.2⟩,rfl⟩
    rw [supportNegativeCount_eq_weight,p.2.prop.1]; norm_num

def mclTriangleParameterMap (p : (t : Fin 4) × McLTriangleParameters t) : McLTriangles :=
  ⟨mclTriangleParameterVector p.1 p.2,
    mcl_triangle_shape_sound p.1 _ (mcl_triangle_parameter_shape p.1 p.2)⟩

theorem mcl_triangle_parameter_represents (t : Fin 4) (y : leech)
    (hy : McLTriangleShape t y) : ∃ p : McLTriangleParameters t,
      mclTriangleParameterVector t p = y := by
  fin_cases t
  · exact ⟨PUnit.unit,hy.symm⟩
  · obtain ⟨c,hw,ha,hp,he⟩ := hy
    exact ⟨⟨c,hw,ha,hp⟩,he.symm⟩
  · obtain ⟨b,c,hb,hbp,hw,ha,hp,hc,he⟩ := hy
    exact ⟨⟨⟨c,hw,ha,hp⟩,⟨b,hb,hbp,hc⟩⟩,he.symm⟩
  · obtain ⟨T,hT,s,ha,hn,⟨hp,hs⟩,he⟩ := hy
    have hw : hammingNorm s = 2 := by rw [supportNegativeCount_eq_weight] at hn; omega
    exact ⟨⟨⟨T,Finset.mem_filter.mpr ⟨hT,ha,hp⟩⟩,⟨s,hw,hs⟩⟩,Subtype.ext he.symm⟩

theorem mclTriangleParameterMap_surjective : Function.Surjective mclTriangleParameterMap := by
  intro y
  obtain ⟨t,ht⟩ := mcl_triangle_shape_exhaustive y
  obtain ⟨p,hp⟩ := mcl_triangle_parameter_represents t y.val ht
  exact ⟨⟨t,p⟩,Subtype.ext hp⟩

theorem mclTriangleParameterVector_injective (t : Fin 4) :
    Function.Injective (mclTriangleParameterVector t) := by
  fin_cases t
  · intro p q _; exact Subsingleton.elim p q
  · intro p q h
    exact Subtype.ext (oddMinimumVector_injective_parameters _ _ p.val q.val h).2
  · rintro ⟨c,b⟩ ⟨d,e⟩ h
    obtain ⟨hb,hc⟩ := oddMinimumVector_injective_parameters b.val e.val c.val d.val h
    have hcd : c = d := Subtype.ext hc
    subst d
    have hbe : b = e := Subtype.ext hb
    subst e
    rfl
  · rintro ⟨T,s⟩ ⟨U,r⟩ h
    have hTU : T = U := Subtype.ext (by
      have he := congrArg (fun y : leech => evenMagnitudeSupport y.val 2) h
      simp only [mclTriangleParameterVector] at he
      simpa only [co3SignedOctadVector_support] using he)
    subst U
    have hsr : s = r := Subtype.ext (signedSupport_injective T.val (by
      funext i
      have hi := congrArg (fun y : leech => y.val i) h
      change 2*signedSupport T.val s.val i = 2*signedSupport T.val r.val i at hi
      omega))
    subst r
    rfl

theorem mclTriangleParameterMap_injective : Function.Injective mclTriangleParameterMap := by
  rintro ⟨s,p⟩ ⟨t,q⟩ h
  have he := congrArg Subtype.val h
  change mclTriangleParameterVector s p = mclTriangleParameterVector t q at he
  have hq := mcl_triangle_parameter_shape t q
  rw [← he] at hq
  have ht := mcl_triangle_shape_unique s t _ (mcl_triangle_parameter_shape s p) hq
  subst t
  have hp := mclTriangleParameterVector_injective s he
  subst q
  rfl

def mclTriangleParameterEquiv : ((t : Fin 4) × McLTriangleParameters t) ≃ McLTriangles :=
  Equiv.ofBijective mclTriangleParameterMap
    ⟨mclTriangleParameterMap_injective,mclTriangleParameterMap_surjective⟩

end Atlas.Conway
