module

public import CFSG.Quasithin.ChapterE.Section04.Basic
public import Theory.Representation.MathieuCodeRestriction

/-!
# The code/cocode restriction step in E.4.3(3)

The actual point-stabilizer embedding restricts the eleven-dimensional M₂₄
quotients to their M₂₃ modules. An intertwining linear equivalence transfers
the fixed-space parameter to any isomorphic module. Thus the corresponding
M₂₄ bound implies the M₂₃ bound.

The numerical bounds for M₂₄ remain explicit inputs, to be discharged by the
E.4.3 assembly owner. These restriction lemmas do not assert E.4.3(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.4.3,
printed pp.241–242, using the definitions in H.13.1, printed p.395.
-/

public section

namespace CFSG.Quasithin.ChapterE
open MathieuCode

/-- Restricting the actual M₂₄ code cannot increase the fixed-space parameter. -/
theorem moduleA_m23Code_le : moduleA m23CodeRepresentation ≤ moduleA codeRepresentation :=
  moduleA_comp_le codeRepresentation pointEmbedding pointEmbedding_injective

/-- Restricting the actual M₂₄ cocode cannot increase the fixed-space parameter. -/
theorem moduleA_m23Cocode_le :
    moduleA m23CocodeRepresentation ≤ moduleA cocodeRepresentation :=
  moduleA_comp_le cocodeRepresentation pointEmbedding pointEmbedding_injective

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The source code predicate transports through an actual equivariant embedding. -/
theorem moduleA_le_m24Code_of_isM23Code (h : IsM23Code ρ) :
    moduleA ρ ≤ moduleA codeRepresentation := by
  obtain ⟨e, E, hE⟩ := h
  exact moduleA_le_of_equivariant_injective ρ codeRepresentation
    (pointEmbedding.comp e.toMonoidHom) (pointEmbedding_injective.comp e.injective) E hE

/-- The source cocode predicate transports through an actual equivariant embedding. -/
theorem moduleA_le_m24Cocode_of_isM23Cocode (h : IsM23Cocode ρ) :
    moduleA ρ ≤ moduleA cocodeRepresentation := by
  obtain ⟨e, E, hE⟩ := h
  exact moduleA_le_of_equivariant_injective ρ cocodeRepresentation
    (pointEmbedding.comp e.toMonoidHom) (pointEmbedding_injective.comp e.injective) E hE

/-- The code case of E.4.3(3), with the M₂₄ numerical bound explicit. -/
theorem moduleA_le_three_of_isM23Code (h : IsM23Code ρ)
    (h24 : moduleA codeRepresentation ≤ 3) : moduleA ρ ≤ 3 :=
  (moduleA_le_m24Code_of_isM23Code ρ h).trans h24

/-- The cocode case of E.4.3(3), with the M₂₄ numerical bound explicit. -/
theorem moduleA_le_three_of_isM23Cocode (h : IsM23Cocode ρ)
    (h24 : moduleA cocodeRepresentation ≤ 3) : moduleA ρ ≤ 3 :=
  (moduleA_le_m24Cocode_of_isM23Cocode ρ h).trans h24

end CFSG.Quasithin.ChapterE
