module
public import Theory.SpecificGroups.SymplecticFour.Sylow.QuotientActors
public import Theory.GroupTheory.CentralQuotientAutomorphismTransport

/-!
# Intrinsic symplectic Sylow actors on an abstract carrier

Transport a marked symplectic unipotent model and its literal actor through
an isomorphism. The center-quotient faithfulness is preserved, so the quadratic
square-map cyclicity result applies to the original group without any extra
coordinate-action assumption.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.QuotientActors
variable {F R A : Type*} [Field F] [Finite F] [CharP F 2]
variable [Group R] [Group A] [Finite A]

theorem isCyclic_of_faithful_centerQuotient {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 2<n) (e : R≃*unipotent (F:=F))
    (hA : IsPGroup 2 A) (α : A→*MulAut R)
    (hfaithful : Function.Injective ((Subgroup.quotientAut (Subgroup.center R)).comp α)) :
    IsCyclic A := by
  exact isCyclic_of_faithful_unipotent_centerQuotient hF hn hA
    ((MulAut.congr e).toMonoidHom.comp α)
    (e.injective_centerQuotientAction_congr α hfaithful)
end Theory.SpecificGroups.SymplecticFour.QuotientActors
