module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Geometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Orbit

/-!
# Generation from the coset table and the actual Borel

The checked table is transitive. Once it is realized by distinct canonical
cosets and the given count makes it complete, the generated subgroup acts
transitively on all cosets. If it contains the actual Borel, every group
element is a product of an element of that subgroup and a Borel element.
This proves whole-group generation without an independent group-order or
simplicity calculation. Only containment of the full Borel remains a separate
matrix-word obligation.

Source: the literal Borel and permutation table in
`MiddleFactors/source/standard_flag_data.txt`; Guralnick–Malle Proposition 4.3.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization

/-- Transport containment of the literal root-and-full-torus Borel. -/
theorem canonicalBorel_le_generated
    (hB : tableBorel ≤ Subgroup.closure (Set.range tableActor)) :
    canonicalBorel ≤ Subgroup.closure (Set.range actor) := by
  let H := Subgroup.closure (Set.range actor)
  have hle : Subgroup.closure (Set.range tableActor) ≤ H.comap canonicalEquiv.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self j)
  intro b hb
  have hb' : canonicalEquiv.symm b ∈ tableBorel :=
    (canonicalEquiv_borel _).mp (by simpa only [canonicalEquiv.apply_symm_apply] using hb)
  have hm := hle (hB hb')
  change canonicalEquiv (canonicalEquiv.symm b) ∈ H at hm
  simpa only [canonicalEquiv.apply_symm_apply] using hm

/-- Table transitivity is realized by words in the actual two actors. -/
theorem CosetEnumeration.reachable (c : CosetEnumeration) (i : Fin 126) :
    ∃ g ∈ Subgroup.closure (Set.range actor), g • c.point 0 = c.point i := by
  let H := Subgroup.closure (Set.range actor)
  apply table_image_induction (fun k => ∃ g ∈ H, g • c.point 0 = c.point k) ?_ ?_ i
  · exact ⟨1, H.one_mem, one_smul _ _⟩
  · rintro j k ⟨g, hg, he⟩
    refine ⟨(actor j)⁻¹ * g,
      H.mul_mem (H.inv_mem (Subgroup.subset_closure (Set.mem_range_self j))) hg, ?_⟩
    rw [mul_smul, he, ← c.action]

/-- The supplied coset count and Borel containment prove whole-group generation. -/
theorem CosetEnumeration.generates_of_borel (c : CosetEnumeration)
    (hcard : Nat.card CanonicalPoints = 126)
    (hB : tableBorel ≤ Subgroup.closure (Set.range tableActor)) :
    Subgroup.closure (Set.range actor) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨i, hi⟩ := (c.equiv hcard).surjective (QuotientGroup.mk g)
  change c.point i = QuotientGroup.mk g at hi
  obtain ⟨h, hh, he⟩ := c.reachable i
  have heq : (QuotientGroup.mk h : CanonicalPoints) = QuotientGroup.mk g := by
    have he' := he.trans hi
    rw [c.base] at he'
    change QuotientGroup.mk (h * 1) = QuotientGroup.mk g at he'
    simpa only [mul_one] using he'
  have hb : h⁻¹ * g ∈ canonicalBorel := QuotientGroup.leftRel_apply.mp (Quotient.exact heq)
  have hm := (Subgroup.closure (Set.range actor)).mul_mem hh (canonicalBorel_le_generated hB hb)
  simpa only [mul_inv_cancel_left] using hm

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
