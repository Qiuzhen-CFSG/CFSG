/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleParameterInjective.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleShapeIndex
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleParameterInjective.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem oddMinimumVector_injective_parameters (a b : Omega) (c d : golay)
    (h : oddMinimumVector a c = oddMinimumVector b d) : a = b ∧ c = d := by
  have hp := noFiveVector_injective 1 (a₁ := (⟨{a},by simp⟩,c))
    (a₂ := (⟨{b},by simp⟩,d)) (congrArg Subtype.val h)
  exact ⟨Finset.singleton_injective (congrArg (fun x : NoFiveParameters 1 => x.1.val) hp),
    congrArg (fun x : NoFiveParameters 1 => x.2) hp⟩

theorem co3SignedOctadVector_support (T : Finset Omega) (hT : T ∈ octads)
    (s : T → Bit) (hs : (∑ i, s i) = 0) :
    evenMagnitudeSupport (co3SignedOctadVector T hT s hs).val 2 = T :=
  disjointOctadVector_support ∅ ⟨⟨T,hT,Finset.disjoint_empty_right _⟩,⟨s,hs⟩⟩

theorem co3TriangleParameterVector_injective (a : Omega) (t : Fin 8) :
    Function.Injective (co3TriangleParameterVector a t) := by
  fin_cases t
  · intro p q _; exact Subsingleton.elim p q
  · intro p q h
    exact Subtype.ext (constantSupport_injective 4 (by decide) (congrArg Subtype.val h))
  · intro p q h
    exact Subtype.ext (oddMinimumVector_injective_parameters a a p.val q.val h).2
  · rintro ⟨c,b⟩ ⟨d,e⟩ h
    obtain ⟨hb,hc⟩ := oddMinimumVector_injective_parameters b.val e.val c.val d.val h
    have hcd : c = d := Subtype.ext hc
    subst d
    have hbe : b = e := Subtype.ext hb
    subst e
    rfl
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
      simp only [co3TriangleParameterVector] at he
      simpa only [co3SignedOctadVector_support] using he)
    subst U
    have hsr : s = r := Subtype.ext (signedSupport_injective T.val (by
      funext i
      have hi := congrArg (fun y : leech => y.val i) h
      change 2*signedSupport T.val s.val i = 2*signedSupport T.val r.val i at hi
      omega))
    subst r
    rfl
  · rintro ⟨T,s⟩ ⟨U,r⟩ h
    have hTU : T = U := Subtype.ext (by
      have he := congrArg (fun y : leech => evenMagnitudeSupport y.val 2) h
      simp only [co3TriangleParameterVector] at he
      simpa only [co3SignedOctadVector_support] using he)
    subst U
    have hsr : s = r := Subtype.ext (signedSupport_injective T.val (by
      funext i
      have hi := congrArg (fun y : leech => y.val i) h
      change 2*signedSupport T.val s.val i = 2*signedSupport T.val r.val i at hi
      omega))
    subst r
    rfl
  · rintro ⟨c,b⟩ ⟨d,e⟩ h
    obtain ⟨hb,hc⟩ := oddMinimumVector_injective_parameters b.val e.val c.val d.val h
    have hcd : c = d := Subtype.ext hc
    subst d
    have hbe : b = e := Subtype.ext hb
    subst e
    rfl

theorem co3TriangleParameterMap_injective (a : Omega) : Function.Injective (co3TriangleParameterMap a) := by
  rintro ⟨s,p⟩ ⟨t,q⟩ h
  have he := congrArg Subtype.val h
  change co3TriangleParameterVector a s p = co3TriangleParameterVector a t q at he
  have hq := co3_triangle_parameter_shape a t q
  rw [← he] at hq
  have ht : s = t := co3_triangle_shape_unique a s t _ (co3_triangle_parameter_shape a s p)
    hq
  subst t
  have hp : p = q := co3TriangleParameterVector_injective a s he
  subst q
  rfl

end Atlas.Conway
