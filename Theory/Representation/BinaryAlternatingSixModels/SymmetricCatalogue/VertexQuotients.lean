module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.VertexQuotients.Relations
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.VertexQuotients.Incidence
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Reduction

/-!
# Simple quotients of the two fifteen-dimensional S₆ modules

A simple quotient surviving on constants or the natural complement is
recognized by that submodule. Otherwise, composing with the incidence map
is either zero, imposing the five-dimensional line-relation quotient, or
nonzero and kills the opposite incidence map. The latter case imposes the
opposite relation quotient, identified through the actual marked diagram
automorphism. Both cases give genuine equivariant equivalences.

The two vertex theorems discharge `hPoint` and `hLine` in
`classify_of_incidence_maps`. The final application retains only the independent
tensor irreducibility and incidence-cohomology comparison, whose construction
belongs to the catalogue assembly. No exhaustion or character table is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–3,
printed pp.342–345 (PDF pp.353–356).
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open BinaryDuadStructure Representation
namespace BinaryAlternatingSix.SymmetricCatalogue
open VertexQuotients

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem point_relations_recognize
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (f : pointAction.IntertwiningMap ρ) (hf : f ≠ 0) (hl : ∀ s, f (line s) = 0) :
    Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) := by
  exact point_relations (MulEquiv.refl S6) ρ f hf hl

private theorem line_relations_recognize
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (f : lineRepresentation.IntertwiningMap ρ) (hf : f ≠ 0) (hl : ∀ d, f (pencil d) = 0) :
    Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv secondNatural) := by
  let q := f.comp lineRelabelEquiv.toIntertwiningMap
  have hq : q ≠ 0 := by
    intro h
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    obtain ⟨v, rfl⟩ := lineRelabel.surjective u
    exact congrArg (fun z : IntertwiningMap (pointAction.comp diagramAut.toMonoidHom) ρ => z v) h
  apply point_relations diagramAut ρ q hq
  intro s
  change f (lineRelabel (line s)) = 0
  rw [lineRelabel_line, hl]

/-- Every simple quotient of the fifteen-point S₆ module is one of the three
small marked models. This supplies `hPoint` in `classify_of_incidence_maps`. -/
theorem point_quotient_alternatives
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (f : pointAction.IntertwiningMap ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
      Nonempty (ρ.Equiv secondNatural) := by
  by_cases hc : f (allOne Duad) = 0
  · by_cases hn : f.comp pointNaturalEmbedding = 0
    · have hnat (v : NaturalModule) : f (complementMap v) = 0 :=
        congrArg (fun q : firstNatural.IntertwiningMap ρ => q v) hn
      by_cases hb : f.comp incidence = 0
      · have hl (s : Syntheme) : f (line s) = 0 := by
          have he := congrArg (fun q : lineRepresentation.IntertwiningMap ρ =>
            q (Pi.single s 1)) hb
          change f (incidenceLinear (Pi.single s 1)) = 0 at he
          simpa only [incidence_single] using he
        exact (point_relations_recognize ρ f hf hl).imp_right Or.inl
      · have hl (d : Duad) : (f.comp incidence) (pencil d) = 0 := by
          change f (incidenceLinear (pencil d)) = 0
          rw [← transpose_single, incidence_square_single, map_add, hc, hnat, add_zero]
        rcases line_relations_recognize ρ (f.comp incidence) hb hl with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · let := firstNatural_irreducible
      exact Or.inr (Or.inl (equiv_of_nonzero (f.comp pointNaturalEmbedding) hn))
  · exact Or.inl (trivial_of_fixed ρ (f (allOne Duad)) hc (fun g => by
      rw [← f.isIntertwining]
      rfl))

/-- Every simple quotient of the fifteen-line S₆ module is one of the three
small marked models. This supplies `hLine` in `classify_of_incidence_maps`. -/
theorem line_quotient_alternatives
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (f : lineRepresentation.IntertwiningMap ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
      Nonempty (ρ.Equiv secondNatural) := by
  by_cases hc : f (allOne Syntheme) = 0
  · by_cases hn : f.comp lineNaturalEmbedding = 0
    · have hnat (v : NaturalModule) : f (lineRelabel (complementMap v)) = 0 :=
        congrArg (fun q : secondNatural.IntertwiningMap ρ => q v) hn
      by_cases hb : f.comp incidenceTranspose = 0
      · have hl (d : Duad) : f (pencil d) = 0 := by
          have he := congrArg (fun q : pointAction.IntertwiningMap ρ =>
            q (Pi.single d 1)) hb
          change f (transposeLinear (Pi.single d 1)) = 0 at he
          simpa only [transpose_single] using he
        exact (line_relations_recognize ρ f hf hl).imp_right Or.inr
      · have hl (s : Syntheme) : (f.comp incidenceTranspose) (line s) = 0 := by
          change f (transposeLinear (line s)) = 0
          rw [← incidence_single, transpose_square_single, map_add, hc, hnat, add_zero]
        rcases point_relations_recognize ρ (f.comp incidenceTranspose) hb hl with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · let := secondNatural_irreducible
      exact Or.inr (Or.inr (equiv_of_nonzero (f.comp lineNaturalEmbedding) hn))
  · exact Or.inl (trivial_of_fixed ρ (f (allOne Syntheme)) hc (fun g => by
      rw [← f.isIntertwining]
      rfl))

/-- Apply both vertex calculations to the literal catalogue reduction. Only the
independent tensor irreducibility and top-cohomology comparison remain. -/
theorem classify_of_topCohomology_equiv
    (hTensor : IsIrreducible alternatingTensor)
    (e : topCohomologyRepresentation.Equiv tensorAction)
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ] :
    IsSymmetricModel ρ :=
  classify_of_incidence_maps hTensor e ρ
    (point_quotient_alternatives ρ) (line_quotient_alternatives ρ)

end BinaryAlternatingSix.SymmetricCatalogue
