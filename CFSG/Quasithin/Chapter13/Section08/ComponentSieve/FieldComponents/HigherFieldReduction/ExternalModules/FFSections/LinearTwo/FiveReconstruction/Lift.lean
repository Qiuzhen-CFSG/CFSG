module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.SectionModel

/-!
# Lifting the exceptional section coordinates

When the actual lower space vanishes, its quotient projection is a linear
equivalence. Composing it with the marked section tensor coordinates gives
coordinates for the upper space, intertwining K and the chosen S₃. A
separate transport handles equality of the upper space with the whole
module; that equality remains an explicit premise of this transport.

Source: the section-to-module deduction in Aschbacher–Smith 13.8.20,
printed p.954 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

variable {G U E N : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
    [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G U) (K : Subgroup G)
    (σ : Representation (ZMod 2) E N) (J L : Subgroup E)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5)))
    (s : S₃ →* G) (hs : ∀ (k : K) g, Commute (k : G) (s g))
    (C W : Subrepresentation ρ)

/-- When the central bottom vanishes, the literal section map is an equivalence. -/
def upperSectionEquiv (hC : C = ⊥) : W.toSubmodule ≃ₗ[ZMod 2] SectionSpace ρ C W :=
  LinearEquiv.ofBijective (C.toSubmodule.comap W.toSubmodule.subtype).mkQ ⟨by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    apply Subtype.ext
    have hz := (Submodule.Quotient.mk_eq_zero _).mp hv
    change v.val ∈ C.toSubmodule at hz
    rw [hC] at hz
    exact hz,
    Submodule.mkQ_surjective _⟩

/-- Lift the section coordinates to the upper space using the proved vanishing.
No equality between the upper space and the whole module is used. -/
def upperFactorCoordinates
    (hC : C = ⊥) (b : K ≃* L)
    (a : SectionMultiplicity ρ s C W ≃ₗ[ZMod 2] N)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ K.subtype s hs C W k v) = σ (b k) (a v)) :
    FactorCoordinates W.toRepresentation K s where
  component := componentEquiv σ J L e b
  moduleEquiv := (upperSectionEquiv ρ C W hC).trans
    (sectionCoordinates σ J L e ρ s C W a hgen)
  intertwines k g v :=
    sectionCoordinates_equivariant σ J L e ρ K s hs C W b a hgen ha k g
      (Submodule.Quotient.mk v)

/-- Transport the constructed factor action to the whole module once generation
has been proved. This helper does not assert that generation. -/
def factorCoordinatesOfTop (hW : W.toSubmodule = ⊤)
    (c : FactorCoordinates W.toRepresentation K s) : FactorCoordinates ρ K s := by
  let f : W.toSubmodule ≃ₗ[ZMod 2] U :=
    LinearEquiv.ofBijective W.toSubmodule.subtype
      ⟨W.toSubmodule.subtype_injective, fun v => ⟨⟨v, hW ▸ Submodule.mem_top⟩, rfl⟩⟩
  refine ⟨c.component, f.symm.trans c.moduleEquiv, ?_⟩
  intro k g v
  obtain ⟨w, rfl⟩ := f.surjective v
  change c.moduleEquiv (f.symm (ρ (k.val * s g) (f w))) =
    BinaryPermutation.FiveTensorQuadratic.tensorAction
      (BinaryPermutation.coreRepresentation (Fin 3))
      ((c.component k).val, g) (c.moduleEquiv (f.symm (f w)))
  rw [show ρ (k.val * s g) (f w) = f (W.toRepresentation (k.val * s g) w) from rfl,
    f.symm_apply_apply, f.symm_apply_apply]
  exact c.intertwines k g w

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

end
