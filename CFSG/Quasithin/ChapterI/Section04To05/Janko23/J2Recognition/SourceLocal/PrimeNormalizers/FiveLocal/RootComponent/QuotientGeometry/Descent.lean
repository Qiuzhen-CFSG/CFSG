module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import Theory.GroupTheory.CentralFiveQuotientInvolutions

/-!
# Local inputs to the root-five quotient involution geometry

The two intermediate predicates isolate the source calculations in the group
M = C_G(E): its root-involution centralizer has order twenty and exponent
dividing ten, and all involutions of M are conjugate. The central-five descent
theorem then gives the exact involution data for the literal quotient M/E,
including an equivalence of its full involution centralizer with the four-group.

These predicates remain proof obligations of the source argument. They are not
hypotheses of the intended conclusion of Aschbacher, *Sporadic Groups* (1994),
47.2(2), printed p.261. Their construction uses the marked 47.1 geometry.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent

variable {G : Type*} [Group G] [Finite G]

/-- The two numerical consequences of `C_M(t) = U(t) × E`, before quotienting. -/
def LocalCentralizerBounds (t : G) : Prop :=
  ∀ (E : Subgroup G), Nat.card E = 5 → ∀ hEt : E ≤ involutionCentralizer t,
    Nat.card (centralizer ({rootInCentralizer E t hEt} : Set (centralizer (E : Set G)))) = 20 ∧
    ∀ x : centralizer ({rootInCentralizer E t hEt} : Set (centralizer (E : Set G))),
      x ^ 10 = 1

/-- Fusion in the literal five-centralizer, before quotienting. This is to be
proved by Sylow placement into `U(t)` and the marked A₄ action. -/
def LocalInvolutionFusion (t : G) : Prop :=
  ∀ (E : Subgroup G), Nat.card E = 5 → ∀ hEt : E ≤ involutionCentralizer t,
    ∀ x : centralizer (E : Set G), orderOf x = 2 →
      IsConj x (rootInCentralizer E t hEt)

/-- The two prequotient calculations supply the full BSW involution data. -/
theorem quotientInvolutionData_of_centralizer (E : Subgroup G) (hE : Nat.card E = 5)
    (t : G) (ht : orderOf t = 2) (hEt : E ≤ involutionCentralizer t)
    (hc : Nat.card (centralizer ({rootInCentralizer E t hEt} :
      Set (centralizer (E : Set G)))) = 20)
    (hp : ∀ x : centralizer ({rootInCentralizer E t hEt} :
      Set (centralizer (E : Set G))), x ^ 10 = 1)
    (hf : ∀ x : centralizer (E : Set G), orderOf x = 2 →
      IsConj x (rootInCentralizer E t hEt)) :
    Nonempty (QuotientInvolutionData E t hEt) := by
  have htm : orderOf (rootInCentralizer E t hEt) = 2 :=
    (orderOf_coe _).symm.trans ht
  obtain ⟨_, hfusion, hequiv⟩ := Theory.GroupTheory.CentralFiveQuotient.involution_geometry
    (kernel E) (kernel_le_center E) (kernel_card E hE)
    (rootInCentralizer E t hEt) htm hc hp hf
  exact ⟨⟨hfusion, hequiv⟩⟩

/-- Specialization to the local predicates at a fixed representative. -/
theorem quotientInvolutionData_of_local (t : G) (ht : orderOf t = 2)
    (hC : LocalCentralizerBounds t) (hF : LocalInvolutionFusion t)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer t) :
    Nonempty (QuotientInvolutionData E t hEt) :=
  quotientInvolutionData_of_centralizer E hE t ht hEt
    (hC E hE hEt).1 (hC E hE hEt).2 (hF E hE hEt)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
