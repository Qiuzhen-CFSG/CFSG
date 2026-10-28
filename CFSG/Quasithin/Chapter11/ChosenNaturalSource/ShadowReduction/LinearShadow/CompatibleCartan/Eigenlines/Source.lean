module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Fields
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Nonzero
/-!
# The nonzero common-field commutator on the original seed

The actual invariant complements yield a nonzero central commutator in V₂.
The Y-linear conjugation action constructs its P-subspace, and scalar
agreement on P ∩ V constructs its V-subspace with the same ambient image.
All inputs refer to the original D, S, flag, radical and Y = ⟨L₂,I⟩.

The earlier geometry and separate marked sections are explicit inputs;
SourceFields constructs their compatible scalar agreement. Neither Cartan
scalar families nor the final eigenvalues are asserted by this module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the
paragraph following 11.3.8, printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {P I X : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
    [Module S.field.Carrier (Additive P)] [Module S.field.Carrier (Additive V)]

/-- Both actual field subspaces of the nonzero commutator, with source centrality
and Cartan normalization derived from the invariant complements. -/
theorem source_commutator_field_spaces
    (hcommon : ∀ (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)),
      ((a • (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
        ((a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P))
    (hρ : ∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
      ((ρ y p).toMul : G) = (MulAut.conj (y : G)) (p.toMul : G))
    (hPV : P ⊓ V = f.Vi 1)
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (hproper : P ⊓ f.Ri 0 < P)
    (hP : P = (f.Li 1).pCoreIn 2) (hVY : V ≤ f.Li 1 ⊔ I)
    (hYP : f.Li 1 ⊔ I ≤ normalizer (P : Set G))
    (U₁ : Submodule S.field.Carrier (Additive V))
    (U₂ : Submodule S.field.Carrier (Additive P))
    (hs₁ : f.Vi 1 ⊔ ambientSubgroup U₁ = V)
    (hs₂ : (P ⊓ f.Ri 0) ⊔ ambientSubgroup U₂ = P)
    (hn₁ : X ≤ normalizer (ambientSubgroup U₁ : Set G))
    (hn₂ : X ≤ normalizer (ambientSubgroup U₂ : Set G)) :
    ∃ Cₚ : Submodule S.field.Carrier (Additive P),
      ∃ Cᵥ : Submodule S.field.Carrier (Additive V),
        ambientSubgroup Cₚ = ⁅ambientSubgroup U₁, ambientSubgroup U₂⁆ ∧
        ambientSubgroup Cᵥ = ⁅ambientSubgroup U₁, ambientSubgroup U₂⁆ ∧
        ambientSubgroup Cₚ ≠ ⊥ ∧ ambientSubgroup Cₚ ≤ f.Vi 1 ∧
        ambientSubgroup Cₚ ≤ centralizer ((ambientSubgroup U₁ ⊔ ambientSubgroup U₂ : Subgroup G) : Set G) ∧
        X ≤ normalizer (ambientSubgroup Cₚ : Set G) := by
  have hW₁Y : ambientSubgroup U₁ ≤ f.Li 1 ⊔ I := (map_subtype_le _).trans hVY
  let Cₚ := commutatorFieldSpace ρ hW₁Y U₂
  have he : ambientSubgroup Cₚ = ⁅ambientSubgroup U₁, ambientSubgroup U₂⁆ :=
    ambient_commutatorFieldSpace ρ hρ hW₁Y U₂
  have hc := source_complement_commutator D S f hPV hfixed hproper hP hVY hYP hs₁ hs₂ hn₁ hn₂
  have hCV : ambientSubgroup Cₚ ≤ V := he ▸ hc.2.1.trans (D.centralQuotientPreimage_le _)
  refine ⟨Cₚ, commonFieldSpace hcommon Cₚ, he,
    (ambient_commonFieldSpace hcommon Cₚ hCV).trans he, ?_, ?_, ?_, ?_⟩
  · exact he ▸ hc.1
  · exact he ▸ hc.2.1
  · exact he ▸ hc.2.2.1
  · exact he ▸ hc.2.2.2
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
