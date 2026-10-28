module

public import Theory.SpecificGroups.G2.MultiplierFourBound
public import Theory.SpecificGroups.G2.MultiplierFourBound.OddPrimary
public import Theory.SpecificGroups.G2.MultiplierFourBound.TwoPrimary
public import Theory.SpecificGroups.G2.MultiplierFourBound.TwoPrimary.MixedRelations
public import Theory.SpecificGroups.G2.MultiplierFourBound.TwoPrimary.QuotientSections
public import Theory.GroupTheory.PerfectCentralCoverKernelLowerBound

/-!
# The universal central kernel of G₂(4) has order at most two

Quotient a finite perfect central cover by the defect of its C-root preimage.
The defect is central and has order at most two; all six root defects lie in it.
The quotient therefore has torus-equivariant additive root sections. The
mixed-relations calculation makes their ordered product a section of the
actual positive-unipotent subgroup. Its odd index and transfer exclude a
factor of four in the original kernel.

For the prescribed universal cover, the existing odd-primary exclusions and
cyclic-Sylow transfer finish the order bound. Every other perfect central
cover inherits the bound by universal kernel divisibility. Thus the source
application to a given quasisimple group requires no independent multiplier
premise or construction of a new nontrivial cover.

Source: Aschbacher–Smith I.1.3(1), printed p.407 (PDF p.418), and GLS III §6.1,
Tables 6.1.2–6.1.3. The root-defect and mixed-relation modules provide the
exceptional field-four calculation on the attributed ATLAS octonion model.
-/

namespace Atlas.G2.FiniteCover.MultiplierFourBound

open PerfectCentralCovering TwoPrimary

variable {E : Type*} [Group E]

/-- The common short-root defect is the only possible two-primary obstruction
in a finite perfect central cover of the actual field-four model. -/
public theorem not_four_dvd_card_kernel [Finite E] (c : Cover E FourBase) :
    ¬ 4 ∣ Nat.card c.toMonoidHom.ker := by
  let D := rootDefect c.toMonoidHom 2
  have hD : D ≤ c.toMonoidHom.ker := rootDefect_le_kernel _ _
  obtain ⟨L, hL⟩ := shortRootQuotient_torusEquivariant_sections c
  exact not_four_dvd_card_kernel_of_quotient_positive_relations c D hD
    (rootDefect_card_le_two _ c.surjective c.ker_le_center 2) L
    (MixedRelations.productCompatible_four L
      (c.quotientKernelSubgroup D hD).surjective
      (c.quotientKernelSubgroup D hD).ker_le_center hL)

/-- The exact two-primary bound on the literal universal projection. -/
public theorem not_four_dvd_card_universal_kernel :
    ¬ 4 ∣ Nat.card (Kernel FourField) :=
  not_four_dvd_card_kernel (universalCover FourBase)

/-- The universal central kernel of the octonion group G₂(4) has order at most two. -/
public theorem card_kernel_le_two : Nat.card (Kernel FourField) ≤ 2 :=
  card_kernel_le_two_of_primary_bounds OddPrimary.not_three_dvd_card_kernel
    OddPrimary.not_five_dvd_card_kernel not_four_dvd_card_universal_kernel

/-- Every finite perfect central cover inherits the universal multiplier bound. -/
public theorem cover_kernel_card_le_two (c : Cover E FourBase) :
    Nat.card c.toMonoidHom.ker ≤ 2 :=
  (Nat.le_of_dvd Nat.card_pos c.kernel_card_dvd_universal).trans card_kernel_le_two

end Atlas.G2.FiniteCover.MultiplierFourBound
