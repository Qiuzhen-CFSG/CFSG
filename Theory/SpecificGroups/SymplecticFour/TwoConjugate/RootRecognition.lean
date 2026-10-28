module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry.RootGeneration

/-!
# A bounded root-generation bridge for the actual E.2.7 pair

The source's two-conjugate subgroup is retained literally. Once a coefficient
subfield's actual root groups have been extracted, the matrix Weyl words
produce the full embedded subfield copy of Sp₄. A weaker version starts with
the positive unipotent and one opposite long-root family. The parameter
extraction from one nonzero central-root intersection is deliberately not
asserted here: the rank-one witness may rescale the opposite root, and its
abstract finite-field model does not yet identify that scale with the second
rank-one copy.

Source: Aschbacher--Smith, E.2.7, printed pp.219--221. The generation words
are the literal type-C₂ matrices in `OvergroupGeometry.RootGeneration`.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate

open Matrix Subgroup
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open Representation.OneCohomology.SymplecticFour

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- Every coefficient-root group of a subfield copy lies in the literal ambient
subgroup, so the full embedded subfield symplectic group lies there. -/
theorem coefficientSubfield_le_of_all_roots
    (K : Subfield F) (H : Subgroup (Sp F))
    (hroot : ∀ r : Fin 8, ∀ t : K,
      coefficientInclusion K (rootElement r t) ∈ H) :
    (coefficientInclusion K).range ≤ H := by
  let J : Subgroup (Sp K) := H.comap (coefficientInclusion K)
  have hJ : J = ⊤ := by
    apply eq_top_of_rootElement_mem
    intro r t
    exact hroot r t
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ J := by
    rw [hJ]
    trivial
  exact hy

/-- The positive-unipotent/opposite-long-root route gives the same embedded
subfield copy, using the actual eight-root Weyl generation calculation. -/
theorem coefficientSubfield_le_of_unipotent_and_opposite
    (K : Subfield F) (H : Subgroup (Sp F))
    (hU : (unipotent (F := K)).map (coefficientInclusion K) ≤ H)
    (h₁ : ∀ t : K, coefficientInclusion K (rootElement 1 t) ∈ H) :
    (coefficientInclusion K).range ≤ H := by
  let J : Subgroup (Sp K) := H.comap (coefficientInclusion K)
  have hU' : unipotent (F := K) ≤ J := by
    intro x hx
    exact hU ⟨x, hx, rfl⟩
  have h₁' : ∀ t : K, rootElement 1 t ∈ J := by
    intro t
    exact h₁ t
  have hJ : J = ⊤ :=
    ThreeResidualPlacement.OvergroupGeometry.eq_top_of_unipotent_le_of_opposite_long_root J hU' h₁'
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ J := by
    rw [hJ]
    trivial
  exact hy

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
