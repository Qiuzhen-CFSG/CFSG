module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning.Groups
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The B.5 rows compatible with the actual exchanged component

The intrinsic swapped PSL₂ model excludes every symplectic, G₂, higher binary
linear and exceptional alternating row. The surviving SL₃ field is binary.
All action equivalences, offender families, ratios and extension data remain
on the original B.5 moved section and its central quotient.

Source: Aschbacher--Smith C.2.7(3), pp.145--147, and 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning
open ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The surviving irreducible rows, retaining their literal B.4 action data. -/
inductive IrreducibleCases (L H : Subgroup D) : Prop
  | linearTwo (F : BinaryField) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2))
      (offenders : ∀ A, IsBestOffender ρ A → ∃ S : Sylow 2 L,
        A = (S : Subgroup L).map L.subtype)
      (ratio : quadraticRatio ρ = 1)
  | linearThree (F : BinaryField) (binary : F.degree = 1) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
      (ratio : quadraticRatio ρ = 1 / 2)
  | symmetricFive
      (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 5))
        (alternatingGroup (Fin 5)))
      (offenders : ∀ A, IsBestOffender ρ A →
        ChapterB.Offenders.CaseAFamily 5
          ((A.subgroupOf H).map e.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)

/-- The surviving full B.5 rows; the doubled row is on the moved space itself. -/
inductive Cases (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : IrreducibleCases s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
  | doubleThree (F : BinaryField) (binary : F.degree = 1) (whole : L = ⊤)
      (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
      (offenders : ∀ A, IsBestOffender s.space.toRepresentation A ↔
        IsFullAxisGroup F 3 ((A.subgroupOf L).map e.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)

variable {ρ} [Finite D]

/-- Prune the full B.4 row using the actual component's intrinsic model. -/
theorem irreducible_cases {L H : Subgroup D}
    (hs : Chapter1.XiEmbedding.SwappedModel 3 L)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) : IrreducibleCases ρ L H := by
  cases h with
  | linearTwo F hg e ho hr => exact .linearTwo F hg e ho hr
  | linearThree F hg e hr =>
    exact .linearThree F (slThree_swapped_parameter F.degree_pos F.card_eq e.groupEquiv hs).1 hg e hr
  | symplectic F _ _ e _ => exact (not_symplectic F e.groupEquiv hs).elim
  | symplecticTwo e _ =>
    have hn := alternating_degree (by decide) (by decide)
      ⟨e.subgroupEquiv.trans Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.alternatingDerivedEquiv.symm⟩ hs
    norm_num at hn
  | g2 F _ _ e _ _ => exact (not_g2 F e.groupEquiv hs).elim
  | g2Two e _ _ => exact (not_binaryG2Derived_quotient hs ⟨e.subgroupEquiv⟩).elim
  | symmetric n hn e ho hr =>
    have hn5 := alternating_degree (by omega) (by omega) ⟨e.subgroupEquiv⟩ hs
    subst n
    exact .symmetricFive e ho hr
  | alternatingSix _ e _ _ =>
    have hn := alternating_degree (by decide) (by decide) ⟨e.groupEquiv⟩ hs
    norm_num at hn
  | alternatingSeven _ _ e _ _ _ =>
    have hn := alternating_degree (by decide) (by decide) ⟨e⟩ hs
    norm_num at hn
  | tripleSix _ e _ => exact (not_tripleSix e.centerEquiv e.quotientEquiv hs).elim
  | binaryLinear d hd _ e _ => exact (not_binaryLinear hd e.groupEquiv hs).elim
  | orthogonalSix _ _ e _ _ =>
    have hn := alternating_degree (by decide) (by decide) ⟨e.groupEquiv⟩ hs
    norm_num at hn
  | symmetricEight _ e _ =>
    have hn := alternating_degree (by decide) (by decide) ⟨e.subgroupEquiv⟩ hs
    norm_num at hn
  | exteriorFive _ _ e _ _ _ => exact (not_binaryLinear (Or.inr rfl) e hs).elim

/-- Prune all four B.5 alternatives without discarding central-extension data. -/
theorem quasisimple_cases {L : Subgroup D} {s : MovedSection ρ L}
    (hs : Chapter1.XiEmbedding.SwappedModel 3 L)
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) : Cases ρ L s := by
  cases h with
  | irreducible hi hf hirr hrow he =>
    exact .irreducible hi hf hirr (irreducible_cases hs hrow) he
  | doubleThree F hw e ho hr =>
    exact .doubleThree F (slThree_swapped_parameter F.degree_pos F.card_eq e.groupEquiv hs).1 hw e ho hr
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (not_binaryLinear hd e.groupEquiv hs).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (not_binaryLinear hd e.groupEquiv hs).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning
