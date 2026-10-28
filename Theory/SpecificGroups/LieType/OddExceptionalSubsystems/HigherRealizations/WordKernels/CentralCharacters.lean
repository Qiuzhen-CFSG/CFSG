module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.Reduction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.Source

/-!
# Construction of the E6 central characters

An element of cube one determines a character of the actual E6 weight/root
quotient by its value on the zeroth fundamental weight. This constructs the
characters, rather than assuming them. Consequently the requested comparison
is equivalent to two matrix assertions on source-trivial words: their higher
values have cube one, and the pinned diagram sends those values to inverses.

The accompanying `Words` module proves both assertions for the explicit
central coroot words in the literal E7 and E8 representations. Localization
of arbitrary source relations and diagram compatibility on those relations
remain representation-theoretic obligations; no unconditional comparison is
claimed here.

Source: GLS3 §§1.12 and 2.5–2.6 (`refs/KGroup/GLS3/chapter2.tex`). The word
comparison is used in Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations
namespace CentralCharacters

variable {G : Type*} [Group G]

/-- The character specified by a cubic element at the zeroth fundamental weight. -/
def characterOfCube (g : G) (hg : g ^ 3 = 1) :
    typeE6WeightLatticeQuotient →+ Additive G :=
  (ZMod.lift 3 ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
    change Additive.ofMul (g ^ (3 : ℤ)) = 0
    simpa using congrArg Additive.ofMul hg⟩).comp
      typeE6WeightLatticeQuotientEquiv.toAddMonoidHom

@[simp] theorem characterOfCube_value (g : G) (hg : g ^ 3 = 1) :
    CentralLattice.characterValue (characterOfCube g hg) CentralLattice.centralWeight = g := by
  simp only [CentralLattice.characterValue, characterOfCube, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [CentralLattice.centralWeight_coordinate]
  change Additive.toMul (ZMod.lift 3 _ ((1 : ℤ) : ZMod 3)) = g
  rw [ZMod.lift_coe]
  simp

/-- The same constructed character gives the required diagram value. -/
theorem characterOfCube_diagram (g : G) (hg : g ^ 3 = 1) :
    CentralLattice.characterValue (characterOfCube g hg)
      (CentralLattice.quotientDiagram CentralLattice.centralWeight) = g⁻¹ := by
  rw [CentralLattice.characterValue_diagram, characterOfCube_value]

end CentralCharacters

variable (F : Type*) [Field F]

/-- An exact separation of the two remaining representation obligations. -/
theorem centralCharacterComparison_iff {G : Type*} [Group G]
    (v : SixNodeWord F →* G) :
    CentralCharacterComparison F v ↔
      (∀ w, sourceSix F w = 1 → v w ^ 3 = 1) ∧
      (∀ w, sourceSix F w = 1 → v (diagramWord F w) = (v w)⁻¹) := by
  constructor
  · intro h
    constructor
    · intro w hw
      obtain ⟨c, hc, _⟩ := h w hw
      rw [hc]
      exact CentralLattice.characterValue_cube c _
    · intro w hw
      obtain ⟨c, hc, hd⟩ := h w hw
      rw [hc, hd, CentralLattice.characterValue_diagram]
  · rintro ⟨hcube, hdiagram⟩ w hw
    refine ⟨CentralCharacters.characterOfCube (v w) (hcube w hw), ?_, ?_⟩
    · exact (CentralCharacters.characterOfCube_value _ _).symm
    · rw [CentralCharacters.characterOfCube_diagram]
      exact hdiagram w hw

/-- Assemble the comparison from centrality of the relative kernel and the
center calculation in the actual six-node matrix image. Both inputs must be
proved for the literal representation before this gives an unconditional result. -/
theorem centralCharacterComparison_of_central_kernel {G : Type*} [Group G]
    (v : SixNodeWord F →* G)
    (hkernel : ∀ w, sourceSix F w = 1 → ∀ z, Commute (v w) (v z))
    (hcenter : ∀ w, (∀ z, Commute (v w) (v z)) →
      v w ^ 3 = 1 ∧ v (diagramWord F w) = (v w)⁻¹) :
    CentralCharacterComparison F v := by
  apply (centralCharacterComparison_iff F v).mpr
  exact ⟨fun w hw => (hcenter w (hkernel w hw)).1,
    fun w hw => (hcenter w (hkernel w hw)).2⟩

namespace CentralCharacters

/-- Actual E7 central words realize the required pair of character values. -/
theorem e7_centralWord_character (u : Fˣ) (hu : u ^ 3 = 1) :
    ∃ c : typeE6WeightLatticeQuotient →+ Additive (ExceptionalSplit.e7Cover F),
      e7Six F (centralWord F u) =
        CentralLattice.characterValue c CentralLattice.centralWeight ∧
      e7Six F (diagramWord F (centralWord F u)) =
        CentralLattice.characterValue c
          (CentralLattice.quotientDiagram CentralLattice.centralWeight) := by
  refine ⟨characterOfCube _ (e7Six_centralWord_cube F u hu), ?_, ?_⟩
  · exact (characterOfCube_value _ _).symm
  · rw [characterOfCube_diagram, e7Six_diagram_centralWord F u hu]

/-- Actual E8 central words realize the required pair of character values. -/
theorem e8_centralWord_character (u : Fˣ) (hu : u ^ 3 = 1) :
    ∃ c : typeE6WeightLatticeQuotient →+ Additive (ExceptionalSplit.e8Cover F),
      e8Six F (centralWord F u) =
        CentralLattice.characterValue c CentralLattice.centralWeight ∧
      e8Six F (diagramWord F (centralWord F u)) =
        CentralLattice.characterValue c
          (CentralLattice.quotientDiagram CentralLattice.centralWeight) := by
  refine ⟨characterOfCube _ (e8Six_centralWord_cube F u hu), ?_, ?_⟩
  · exact (characterOfCube_value _ _).symm
  · rw [characterOfCube_diagram, e8Six_diagram_centralWord F u hu]

end CentralCharacters
end TwistedE6.FoldedSubsystem.HigherRealizations
