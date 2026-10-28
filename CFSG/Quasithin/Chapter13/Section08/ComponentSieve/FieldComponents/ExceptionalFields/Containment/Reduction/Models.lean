module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.BorelMarking
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.Representation.HexacodeAction.Cover

/-!
# Actual exceptional models and the intrinsic Borel contract

These are the four carriers left after the separate projective L₃(4)
exclusion in 13.8.20. The unitary parameter eight is the fixed-field
order, so the matrix field has order sixty-four. The local covered case
uses the actual nonsplit hexacode group 3.A₆, as in Components.Models.

`BorelOrderFacts` states only the intrinsic Borel arithmetic needed by the
noncontainment proof. `borelOrderFacts_of_exceptionalModels` in the
`ModelOrders` module constructs it from `ExceptionalModels`; its fields
do not assume any containment, cover recognition, or exceptional reduction
conclusion.
Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
open HigherFieldReduction Chapter1.Section02.LocalModels

/-- Actual equivalences in each of the four exceptional alternatives. -/
def ExceptionalModels (D : Type*) [Group D] : Prop :=
  ClassicalGroup.IsPSL D 2 4 ∨ IsSL D 3 4 ∨
    ClassicalGroup.IsPSU D 3 8 ∨ IsSU D 3 8

/-- The earlier local alternatives, including the actual cover, elementary
nine, and the source choice X = L₁ or L₁,+. -/
def EarlierSeedModels {G : Type*} [Group G] (L L₁ X L₁plus : Subgroup G) : Prop :=
  (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
    Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ∧ X = L₁) ∨
  (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    Nonempty ((L₁ ⧸ pCore 2 L₁) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧ X = L₁plus)

/-- The exact arithmetic contract for the lifted source Borel.
The three-residual is O³; the three-generated subgroup used by the local
proof is the different residual O^{3′}. -/
structure BorelOrderFacts {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hKH : K ≤ H) (S : Sylow 2 K) : Prop where
  threeResidual_coprime : Nat.Coprime 3
    (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S))))
  three_dvd : 3 ∣ Nat.card (borelResidual (componentBorel H K hKH S))
  specialLinear_nine : IsSL (Source.starImage H K) 3 4 →
    9 ∣ Nat.card (borelResidual (componentBorel H K hKH S))
  specialUnitary_nine : IsSU (Source.starImage H K) 3 8 →
    9 ∣ Nat.card (borelResidual (componentBorel H K hKH S))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
