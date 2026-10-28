module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.LocalContracts

/-!
# Complete earlier-source inputs for the B.5.9 preparation

`CoverInput` is all of B.5.2, including component lifts and the generalized
Fitting image. `ComponentInput` is all of B.5.5: normality, every eligible
fixed-core action, a faithful invariant chief section with its literal kernel
quotient and full B.4.2 comparison, the full component list, and the prime-core
and generalized-Fitting conclusions. The triple-cover row specifies the
actual center and central quotient of the quasisimple component. The B.4.2
comparison uses the corrected projective F₄-line convention.

These are universal earlier-source implications, not asserted theorems.
Their producer is qt-b05-quotient-components; final discharge belongs to
qt-b05-general-classification. In particular they contain no assertion
about the smaller moved seed U, no rank-one reduced list, and no B.5.9 result.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.2–B.5.5, printed pp.103–105; B.4.2, printed p.86.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
open QuasisimpleSource
universe u v

/-- All of B.5.2 on an actual finite SQTK cover and its surjection. -/
structure CoverConclusion (K : GroupClass.{u}) (D : Type u) [Group D] where
  Cover : Type u
  [coverGroup : Group Cover]
  [coverFinite : Finite Cover]
  projection : Cover →* D
  surjective : Function.Surjective projection
  sqtk : IsSQTK K Cover
  fitting_nilpotent : Group.IsNilpotent ((fittingSubgroup D).comap projection)
  kernel_nilpotent : Group.IsNilpotent projection.ker
  kernel_odd : Odd (Nat.card projection.ker)
  component_lifts : ∀ L, IsComponent D L →
    ∃ Lhat, IsComponent Cover Lhat ∧ Lhat.map projection = L
  fitting_image : (generalizedFitting Cover).map projection = generalizedFitting D

attribute [instance] CoverConclusion.coverGroup CoverConclusion.coverFinite

/-- The complete universal B.5.2 implication, with no FF-module premise. -/
def CoverInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D], Nonempty (SQTKQuotient K D) →
    Nonempty (CoverConclusion K D)

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The full component list in B.5.5(1iv). The triple cover retains the actual
center and central quotient of the quasisimple component, rather than a family tag. -/
def ComponentModels (L : Subgroup D) : Prop :=
  (∃ F : BinaryField, Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ∨
  (∃ F : BinaryField, Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)) ∨
  (∃ F : BinaryField, Nonempty (L ≃* commutator (Matrix.symplecticGroup (Fin 2) F.Carrier))) ∨
  (∃ F : BinaryField, Nonempty (L ≃* commutator (Atlas.G2.Model F.Carrier))) ∨
  Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
  (Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧
    Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 6))) ∨
  Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
  Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

/-- An actual A-invariant L-chief section of V. The actor here is LA. -/
structure ChiefSection (A L : Subgroup D) where
  upper : Subrepresentation (ρ.comp (L ⊔ A).subtype)
  lower : Subrepresentation upper.toRepresentation
  faithful : Function.Injective (lower.quotientRepresentation.comp
    (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left)))
  irreducible : IsIrreducible (lower.quotientRepresentation.comp
    (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left)))

namespace ChiefSection
variable {ρ} {A L : Subgroup D} (s : ChiefSection ρ A L)
abbrev Actor := (L ⊔ A : Subgroup D) ⧸ s.lower.quotientRepresentation.ker
noncomputable def projection : (L ⊔ A : Subgroup D) →* s.Actor :=
  QuotientGroup.mk' s.lower.quotientRepresentation.ker
noncomputable def action := quotientOfLEKer s.lower.quotientRepresentation
  s.lower.quotientRepresentation.ker le_rfl
noncomputable def component : Subgroup s.Actor := (L.subgroupOf (L ⊔ A)).map s.projection
noncomputable def offender : Subgroup s.Actor := (A.subgroupOf (L ⊔ A)).map s.projection
end ChiefSection

/-- B.5.5(1iii–iv) on that same section, including the full corrected B.4.2
action conclusion and the literal offender and component quotient images. -/
structure ChiefConclusion (A L : Subgroup D) where
  sectionData : ChiefSection ρ A L
  fitting : generalizedFitting sectionData.Actor = sectionData.component
  offender : ∃ B ≤ sectionData.offender, IsBestOffender sectionData.action B
  model : ComponentModels L
  actions : ProjectiveLine.IrreducibleActionCase sectionData.action sectionData.component
    (offenderSubgroup sectionData.action)

/-- Every clause of B.5.5; the fixed-space clause quantifies over every
best offender satisfying [L,A]=L. No moved-seed conclusion occurs here. -/
structure ComponentConclusion : Prop where
  normal : ∀ L, IsComponent D L → L.Normal
  moving : ∀ L, IsComponent D L → ∃ A, IsBestOffender ρ A ∧ ⁅L,A⁆ = L
  fixedCore : ∀ L, IsComponent D L → ∀ A, IsBestOffender ρ A → ⁅L,A⁆ = L →
    (∀ l ∈ L, (∀ w ∈ fixedSpace ρ (localTwoCore L A), ρ l w = w) → l = 1) ∧
    subspaceKernel ρ (fixedSpace ρ (localTwoCore L A)) A = A ⊓ centralizer (L : Set D) ∧
    IsBestOffender (subspaceImageRepresentation ρ (fixedSpace ρ (localTwoCore L A)))
      (restrictedSubgroup ρ (fixedSpace ρ (localTwoCore L A)) A)
  chief : ∀ L, IsComponent D L →
    ∃ A, IsBestOffender ρ A ∧ ⁅L,A⁆ = L ∧ Nonempty (ChiefConclusion ρ A L)
  primeCore_central : ∀ p : ℕ, p.Prime → p ≠ 3 → pCore p D ≤ center D
  fitting : generalizedFitting D = (componentLayer D ⊔ pCore 3 D) ⊔ center D

/-- The complete universal earlier B.5.5 implication. Its original B.5.3
hypotheses are retained, including the actual SQTK quotient presentation. -/
def ComponentInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V), FFHypothesis K ρ → ComponentConclusion ρ
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
