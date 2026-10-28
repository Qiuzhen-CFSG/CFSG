module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly

/-!
# The two intermediate alternatives in 13.8.20

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954
(combined manuscript, 1 March 2004), alternatives (a) and (b).

These shared statements retain the literal star quotient, relative normality
of X in H, inversion inside the component centralizer, and the prescribed
outer conjugation action. The exceptional carriers are specified by genuine
group isomorphisms. In the unitary cases matrices are over a field of order
64 and the involution is x↦x⁸; eight is the fixed-field parameter.

The carrier extraction below removes the extra automorphism-classification
inputs from the torus model witnesses. It proves no local alternative:
BorelAlternative still has to be established from the source setup, and
ExternalXAlternative still has to be excluded before (b) follows.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
universe u v
variable {G : Type u} [Group G]

/-- The literal external-X configuration; normality is only inside H. -/
def ExternalXAlternative (H K X : Subgroup G) : Prop :=
  X ≤ H ∧ ¬ X ≤ K ∧
    Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
    (X.subgroupOf H).Normal ∧
    ∃ c ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)),
      ∀ x ∈ Source.starImage H X, c * x * c⁻¹ = x⁻¹

/-- The prescribed element acts outerly on K*, through its actual conjugation action. -/
def OuterStarAction (H K : Subgroup G) (t : Source.Hstar H) : Prop :=
  ∃ ht : t ∈ normalizer (Source.starImage H K : Set (Source.Hstar H)),
    (Source.starImage H K).normalizerMonoidHom ⟨t, ht⟩ ∉
      MulAut.innerSubgroup (Source.starImage H K)

/-- The five actual special or projective carriers in alternative (b). -/
inductive ExceptionalCarrier (D : Type u) [Group D] : Prop
  | linearTwo (F : Type v) [Field F] [Finite F] [CharP F 2]
      (card : Nat.card F = 4) (equiv : D ≃* PSL(2,F)) : ExceptionalCarrier D
  | specialLinearThree (F : Type v) [Field F] [Finite F] [CharP F 2]
      (card : Nat.card F = 4) (equiv : D ≃* SL(3,F)) : ExceptionalCarrier D
  | projectiveLinearThree (F : Type v) [Field F] [Finite F] [CharP F 2]
      (card : Nat.card F = 4) (equiv : D ≃* PSL(3,F)) : ExceptionalCarrier D
  | specialUnitaryThree (E : Type v) [Field E] [Finite E] (J : HermitianForm 3 E)
      (card : Nat.card E = 64) (conj : ∀ x : E, J.conj x = x ^ 8)
      (equiv : D ≃* J.specialSubgroup) : ExceptionalCarrier D
  | projectiveUnitaryThree (E : Type v) [Field E] [Finite E] (J : HermitianForm 3 E)
      (card : Nat.card E = 64) (conj : ∀ x : E, J.conj x = x ^ 8)
      (equiv : D ≃* ProjectiveSpecialUnitaryMatrixGroup J) : ExceptionalCarrier D

/-- Extract the actual exceptional isomorphisms, discarding the earlier automorphism inputs. -/
theorem exceptionalCarrier_of_torus_models {D : Type u} [Group D]
    (h : TorusModels.Assembly.Model.{u,v} D 2 false true ∨
      TorusModels.Assembly.Model.{u,v} D 3 true false) : ExceptionalCarrier.{u,v} D := by
  rcases h with h | h
  · cases h with
    | linearTwo F hF e _ => exact .linearTwo F hF e
    | specialLinearThree F hF e _ => exact .specialLinearThree F hF e
    | projectiveLinearThree F hF e _ => exact .projectiveLinearThree F hF e
  · cases h with
    | specialUnitaryThree E J hE hconj e _ => exact .specialUnitaryThree E J hE hconj e
    | projectiveUnitaryThree E J hE hconj e _ => exact .projectiveUnitaryThree E J hE hconj e

/-- Alternative (b), with the same prescribed t* as in the local Borel argument. -/
def ExceptionalOuterAlternative (H K : Subgroup G) (t : Source.Hstar H) : Prop :=
  ExceptionalCarrier.{u,v} (Source.starImage H K) ∧ OuterStarAction H K t

/-- The intermediate dichotomy, before external X has been eliminated. -/
def BorelAlternative (H K X : Subgroup G) (t : Source.Hstar H) : Prop :=
  ExternalXAlternative H K X ∨ ExceptionalOuterAlternative.{u,v} H K t

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
end
