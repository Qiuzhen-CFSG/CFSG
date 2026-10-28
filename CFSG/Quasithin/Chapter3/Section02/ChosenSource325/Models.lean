module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# Marked constituent models for D.3.10

The model list uses actual group and binary linear intertwiners. In the
A7 branch the source specifies a four-dimensional representation; its
faithful action on binary four-space is retained explicitly. Module
comparison fixes the original actor and both subgroup inclusions.

D.3.10 explicitly includes the A7 branch separately from natural A6.
The compressed opening list in 3.2.5 omits A7 although its following clause
mentions it. We retain the complete, consistent D.3.10 disjunction.
These definitions specify conclusions and assert no classification.

Source: Aschbacher--Smith D.3.10 and3.2.5, combined manuscript of
1 March 2004, printed pp.201 and580.
-/

@[expose] public section

/-! Literal constituent models in D.3.10(2). -/
open Representation
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
universe u v
variable {A : Type u} [Group A] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The exact D.3.10 list. The A₇ alternative is separate from the natural
A₆ module; it retains actual binary four-space coordinates and its action. -/
def ConstituentModel (ρ : Representation (ZMod 2) A W) : Prop :=
  (∃ F : BinaryField, Nonempty (ActionEquiv ρ (linearNatural F 3))) ∨
  (∃ F : BinaryField, 1 < F.degree ∧ Nonempty
    (ActionEquiv ρ (Representation.restrictScalars (k := ZMod 2)
      (symplecticNatural (k := F.Carrier) 2)))) ∨
  Nonempty (ActionEquiv ρ (alternatingNatural 6)) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    Nonempty (ActionEquiv ρ (linearNatural BinaryField.two n))) ∨
  ∃ σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2),
    Function.Injective σ ∧ Nonempty (ActionEquiv ρ σ)

/-- Equality of the original conjugation modules, expressed using the literal
subgroup inclusions. For elementary abelian two-groups these multiplicative
isomorphisms are exactly binary linear isomorphisms. -/
def SameConjugationModule {G : Type*} [Group G] (L V W : Subgroup G) : Prop :=
  ∃ e : V ≃* W, ∀ (l : L) (v w : V),
    (w : G) = (l : G) * (v : G) * (l : G)⁻¹ →
    (e w : G) = (l : G) * (e v : G) * (l : G)⁻¹

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
