module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Eigenspaces
/-!
# The commutator over the canonical compatible field

Apply the displacement construction using exactly d.compatibleModule and
its unchanged Y-action. The constructed nonzero commutator inherits this
field, and common_smul proves agreement with the original field on V.
This supplies the common-field commutator required by the Cartan argument;
no scalar-family, eigenvalue, pairing or nonvanishing premise is imposed.

The separate plane marking and the preceding fixed-plane/hyperplane
geometry remain explicit, with their source discharge owned by the
compatible-Cartan assembly and marked-section construction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), after
11.3.8, printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G E : Type*} [Group G] [Finite G] [Field E]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {P I X : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
    [Module E (Additive P)] [Module S.field.Carrier (Additive V)]

/-- Apply the proved source commutator construction with the literal ambient scalars. -/
theorem source_canonical_commutator_fields
    (d : SeparatePlaneActions (E := E) (F := S.field.Carrier) P V (f.Li 1))
    (hcard : Nat.card E = Nat.card S.field.Carrier)
    (ρ : Representation E (f.Li 1 ⊔ I : Subgroup G) (Additive P))
    (hρ : ∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
      ((ρ y p).toMul : G) = (MulAut.conj (y : G)) (p.toMul : G))
    (hPV : P ⊓ V = f.Vi 1)
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (hproper : P ⊓ f.Ri 0 < P)
    (hP : P = (f.Li 1).pCoreIn 2) (hVY : V ≤ f.Li 1 ⊔ I)
    (hYP : f.Li 1 ⊔ I ≤ normalizer (P : Set G))
    (U₁ : Submodule S.field.Carrier (Additive V)) :
    letI := d.compatibleModule hcard
    ∀ U₂ : Submodule S.field.Carrier (Additive P),
    f.Vi 1 ⊔ ambientSubgroup U₁ = V →
    (P ⊓ f.Ri 0) ⊔ ambientSubgroup U₂ = P →
    X ≤ normalizer (ambientSubgroup U₁ : Set G) →
    X ≤ normalizer (ambientSubgroup U₂ : Set G) →
    ∃ Cₚ : Submodule S.field.Carrier (Additive P),
      ∃ Cᵥ : Submodule S.field.Carrier (Additive V),
        ∃ hCV : ambientSubgroup Cₚ ≤ V,
          ambientSubgroup Cₚ = ⁅ambientSubgroup U₁, ambientSubgroup U₂⁆ ∧
          ambientSubgroup Cᵥ = ambientSubgroup Cₚ ∧
          ambientSubgroup Cₚ ≠ ⊥ ∧ ambientSubgroup Cₚ ≤ f.Vi 1 ∧
          ambientSubgroup Cₚ ≤ centralizer ((ambientSubgroup U₁ ⊔ ambientSubgroup U₂ : Subgroup G) : Set G) ∧
          X ≤ normalizer (ambientSubgroup Cₚ : Set G) ∧
          (letI := subgroupFieldModule Cₚ rfl
           ∀ (a : S.field.Carrier) (z : Additive (ambientSubgroup Cₚ)),
             ((a • z).toMul : G) =
               ((a • (Subgroup.inclusion hCV).toAdditive z).toMul : G)) := by
  let := d.compatibleModule hcard
  intro U₂ hs₁ hs₂ hn₁ hn₂
  let σ := d.restrictionDatum.compatibleRepresentation hcard ρ
  have hσ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P) :
      ((σ y p).toMul : G) = (MulAut.conj (y : G)) (p.toMul : G) := hρ y p
  obtain ⟨Cₚ, Cᵥ, he, hev, hne, hflag, hz, hn⟩ :=
    source_commutator_field_spaces D S f (d.common_smul hcard) σ hσ hPV hfixed hproper
      hP hVY hYP U₁ U₂ hs₁ hs₂ hn₁ hn₂
  have hCV : ambientSubgroup Cₚ ≤ V := hflag.trans (D.centralQuotientPreimage_le _)
  refine ⟨Cₚ, Cᵥ, hCV, he, hev.trans he.symm, hne, hflag, hz, hn, ?_⟩
  exact subgroupFieldModule_smul_common (d.common_smul hcard) Cₚ rfl hCV
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
