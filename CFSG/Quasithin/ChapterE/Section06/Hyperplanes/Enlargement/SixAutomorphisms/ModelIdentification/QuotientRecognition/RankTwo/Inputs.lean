module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Action
public import Theory.SpecificGroups.SymplecticFour.FieldComponent

/-!
# Intrinsic calculations still needed for the rank-two exclusion

The classical inspection excludes PSL₃ and recognizes the genuine Sp₄(4)
field exception, with an equivalence intertwining the specified involution.
The exceptional inspection excludes G₂, triality, Ree F₄ and the Tits group.
The two small derived endpoints are already treated in `Endpoints`.

The final calculation retains the full ambient source configuration for
Sp₄(4), with the actual A-action identified as its field-involution subgroup.
The elementary order-eight action and pointwise component Sylow fixation
are available from `Action`, but are not asserted to suffice intrinsically.
The source calculation is independent of classifying arbitrary involutions:
the classical inspection supplies its concrete field representative.

These definitions are outstanding proof contracts, not established model facts.
The rank-two assembly remains conditional until all of them are proved.

Source: Aschbacher–Smith, Theorem C and A.2.4, printed p.33; E.6.8,
pp.247–248; E.6.23, p.254; and the intrinsic involution tables in 16.1.4,
pp.1170–1172, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
universe u

/-- An intrinsic exclusion in the literal fixed subgroup of an involution. -/
def ExcludesFixedSix (D : Type*) [Group D] : Prop :=
  ∀ a : MulAut D, orderOf a = 2 → ∀ S : Subgroup D,
    IsComponentIn S a.fixedSubgroup → ¬ Nonempty (S ≃* alternatingGroup (Fin 6))

/-- The ordinary even linear-three family has no fixed A₆ component. -/
def LinearInspection : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
    ∀ f : ℕ, 1 ≤ f → ClassicalGroup.IsPSL D 3 (2 ^ f) → ExcludesFixedSix D

/-- Recognition retains the field exception and its actual involution, rather
than asserting the false blanket symplectic fixed-component exclusion. -/
def SymplecticInspection : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
    ∀ f : ℕ, 2 ≤ f → ClassicalGroup.IsPSp D 2 (2 ^ f) →
    ∀ a : MulAut D, orderOf a = 2 → ∀ S : Subgroup D,
      IsComponentIn S a.fixedSubgroup → Nonempty (S ≃* alternatingGroup (Fin 6)) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 4 ∧ ∃ e : D ≃* Sp F,
          MulAut.congr e a = DiagramAutomorphisms.FieldFixedResidual.representative 1

/-- The four remaining exceptional families, with the actual model predicates.
The binary G₂ derived endpoint is handled separately by Lagrange. -/
def ExceptionalInspection : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
    ((∃ f : ℕ, 2 ≤ f ∧ ClassificationModels.IsG2At D (2 ^ f)) ∨
      (∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2 ^ f) D) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty (D ≃* ReeF4.Model m)) ∨
      Nonempty (D ≃* Tits.ParrottGroup)) → ExcludesFixedSix D

variable {G : Type u} [Group G] [Finite G]

/-- Eliminate the concrete field exception using the full source hypotheses.
The displayed subgroup is the actual A-action under a compatible equivalence;
the original Q remains Sylow only in C_G(A). -/
def SymplecticFieldSourceExclusion (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  HypothesisE61 KnownSimple.IsKnownSimple T M V → HypothesisE615 V →
    EarlierResults T M V →
    ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
      intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      ∀ e : (Y ⧸ center Y) ≃* Sp F,
        ((actionImage A Y).map (quotientAut (center Y))).map (MulAut.congr e).toMonoidHom =
          zpowers (DiagramAutomorphisms.FieldFixedResidual.representative 1) → False

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
