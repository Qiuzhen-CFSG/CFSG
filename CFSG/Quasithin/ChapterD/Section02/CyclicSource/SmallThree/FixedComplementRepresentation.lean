module

public import Theory.Representation.BinaryGroupAction.Subrepresentation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplementCancellation

/-!
# Applying cubic cancellation to the restricted fixed complement

The original D.2.25 residual cubic is detected in the representation on
C_V(Y). Its restricted moved-space dimension two gives a four-element
ambient commutator subgroup through the actual subrepresentation inclusion.
The marked cancellation theorem therefore applies to that same cubic.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.25, printed p.190. The source assembly supplies the common fixed space,
its coprime complement and the residual cubic.
-/


open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The restricted rank-two cubic in D.2.25 supplies precisely the ambient
four-element displacement required by cancellation. -/
public theorem smallThree_fixedComplement_cancellation_of_rank_two
    (hf : Function.Injective ρ) (W : Subrepresentation ρ) (X : Subgroup G) (x : G) :
    letI := BinaryGroupAction.action ρ
    X ∈ smallSupportFactors G (Multiplicative V) 1 →
    x ∈ fittingSubgroup G → x ^ 3 = 1 →
    (∀ z ∈ X, Commute x z) →
    (∀ P ∈ smallSupportFactors G (Multiplicative V) 1, P ≠ X →
      ∀ v ∈ commutatorAction P (Multiplicative V), x • v = v) →
    FixedPoints.subgroup (smallSupportGroup G (Multiplicative V) 1) (Multiplicative V) ⊔
      commutatorAction (smallSupportGroup G (Multiplicative V) 1) (Multiplicative V) = ⊤ →
    BinaryGroupAction.submoduleEquivSubgroup W.toSubmodule =
      FixedPoints.subgroup (smallSupportGroup G (Multiplicative V) 1) (Multiplicative V) →
    Module.finrank (ZMod 2) (subspaceCommutator W.toRepresentation ⊤ (Subgroup.zpowers x)) = 2 →
    False := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ hf
  intro hX hxF hx3 hxX hxother hsplit hW hdim
  apply smallThree_fixedComplement_cancellation hX x hxF hx3 hxX hxother hsplit
  rw [← hW, BinaryGroupAction.subrepresentation_commutator_card, hdim]
  rfl
end CFSG.Quasithin.ChapterD
