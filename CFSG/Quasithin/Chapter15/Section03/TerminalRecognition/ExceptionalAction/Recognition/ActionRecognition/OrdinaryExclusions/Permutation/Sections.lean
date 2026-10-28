module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Seed

/-!
# Natural sections and their injective marked seeds

A potential permutation-model section is an actual moved subrepresentation
modulo its actual fixed subspace, equipped with intertwining coordinates for
the whole quotient group. The seed lies in it by commutator generation and
injects through its central kernel, preserving binary dimension four.

`NaturalSection` is an intermediate contract. Its existence from the complete
FF alternatives, and the concrete local-action obstruction in the model,
remain separate obligations; this module does not exclude S₆ or S₇.

Source: Aschbacher–Smith, B.5.1, printed p.99, and the final proof of
15.3.1, printed p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- A natural action on an actual moved central section of the full quotient.
Its existence is a classification obligation, not a source assumption. -/
structure NaturalSection (n : ℕ) where
  component : Subgroup (coreQuotient H)
  first_le : d.YF.map coreProjection ≤ component
  sectionData : MovedSection
    (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) component
  natural : ActionEquiv sectionData.action (BinaryPermutation.naturalRepresentation (Fin n))

namespace NaturalSection
variable {d} {n : ℕ} (s : NaturalSection d n)

omit [Finite H] in
/-- The literal seed is contained in this moved subrepresentation. -/
theorem vector_le_space : planeSubspace V V ≤ s.sectionData.space.toSubmodule := by
  rw [s.sectionData.space_eq]
  exact vector_le_moved d s.component s.first_le

/-- Inclusion, central projection, and the actual model coordinates. -/
noncomputable def seedMap : planeSubspace V V →ₗ[ZMod 2] BinaryPermutation.natural (Fin n) :=
  s.natural.linearEquiv.toLinearMap.comp (s.sectionData.central.toSubmodule.mkQ.comp
    (Submodule.inclusion s.vector_le_space))

/-- The central kernel cannot kill any vector of the four-dimensional seed. -/
theorem seedMap_injective : Function.Injective s.seedMap := by
  apply s.natural.linearEquiv.injective.comp
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Subtype.ext
  apply (Submodule.disjoint_def.mp (vector_disjoint_fixed d s.component s.first_le))
    v v.property
  have hc : Submodule.inclusion s.vector_le_space v ∈ s.sectionData.central.toSubmodule :=
    (Submodule.Quotient.mk_eq_zero _).mp hv
  rw [s.sectionData.central_eq] at hc
  intro g
  exact congrArg Subtype.val (hc g)

/-- Central passage preserves all four dimensions. -/
theorem seedMap_range_finrank :
    Module.finrank (ZMod 2) (LinearMap.range s.seedMap) = 4 := by
  rw [LinearMap.finrank_range_of_inj s.seedMap_injective]
  exact d.vector_finrank
end NaturalSection

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
