module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.Setup
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex

/-!
# A subgroup route to faithfulness of the Held presentation

Two independent certificates suffice: a generator coset cover by 2058 right
cosets of the source subgroup M₁, and injectivity of the presentation map on
M₁. The cover makes M₁ finite-index. Since M₁ lies in the inverse image of a
point stabilizer of index 2058, strict index monotonicity identifies these
subgroups. The entire kernel therefore lies in M₁, where local injectivity
eliminates it. The argument does not assume the presented group is finite.

Both certificate premises remain explicit and unproved here. In particular,
the ATLAS numerical index claim alone does not prove this module's hypotheses
or presentation faithfulness. The final unconditional faithfulness theorem
still requires both producers.

Source: the subgroup `M1` in John Bray's ATLAS `HeG1-P1.M`, retained in
`Theory/SpecificGroups/Held/Model/Source/`; the standard coset-cover argument
formalized in `Theory.GroupTheory.GeneratorCosetCoverFiniteIndex`.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation

/-- A genuine coset cover identifies the abstract source subgroup with the
inverse image of the concrete point stabilizer. Finiteness of the quotient,
needed for strict index comparison, is derived from the cover. -/
public theorem m1_eq_pointStabilizer_of_cosetCover
    (C : Subgroup.GeneratorCosetCover m1 PresentedGroup.of (Fin 2058)) :
    m1 = pointStabilizer := by
  have : Finite (Presentation ⧸ m1) :=
    C.finite_quotient (PresentedGroup.closure_range_of _)
  have : m1.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hbound : m1.index ≤ 2058 := by
    simpa only [Nat.card_fin] using C.index_le_card (PresentedGroup.closure_range_of _)
  by_contra hne
  have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne m1_le_pointStabilizer hne)
  rw [pointStabilizer_index] at hlt
  exact (Nat.not_lt_of_ge hbound) hlt

/-- The certified index bound places the full presentation kernel in M₁. -/
public theorem presentationMap_ker_le_m1_of_cosetCover
    (C : Subgroup.GeneratorCosetCover m1 PresentedGroup.of (Fin 2058)) :
    presentationMap.ker ≤ m1 := by
  rw [m1_eq_pointStabilizer_of_cosetCover C]
  exact presentationMap.ker_le_comap _

/-- Conditional assembly of the two independent M₁ certificates. This is not
the unconditional faithfulness theorem: both premises still need proofs. -/
public theorem presentationMap_injective_of_m1_certificates
    (C : Subgroup.GeneratorCosetCover m1 PresentedGroup.of (Fin 2058))
    (hlocal : Function.Injective m1Map) : Function.Injective presentationMap := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro g hg
  have hm := presentationMap_ker_le_m1_of_cosetCover C hg
  have he : m1Map ⟨g, hm⟩ = m1Map 1 := by
    simp only [m1Map_apply, map_one]
    exact hg
  exact congrArg Subtype.val (hlocal he)

end Held.CentralCovers.TwoPrimary.FaithfulPresentation
