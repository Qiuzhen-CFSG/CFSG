module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.SpecificGroups.MinusExtraspecial.Model
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The exact local hypotheses for I.4.7

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, printed p. 418, defines `H(2, Ω₄⁻(2))`-type by the
centralizer of an involution. Its intrinsic generalized Fitting subgroup is
`Q₈ * D₈`, the quotient is `A₅`, and the involution is not weakly closed in
that subgroup relative to the ambient finite group.

`localCore` is a subgroup of the centralizer, so its normality and the quotient
are relative to that centralizer. `ambientCore` is its image in the original
group, used for ambient fusion. The concrete central-product model has proved
commuting factor embeddings, generation and the common central involution.
The class-count predicates mean exactly one or two nonempty conjugacy classes
of elements of order two. No simplicity or recognition conclusion is assumed.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

abbrev involutionCentralizer (z : G) : Subgroup G := centralizer ({z} : Set G)

abbrev localCore (z : G) : Subgroup (involutionCentralizer z) :=
  generalizedFitting (involutionCentralizer z)

def ambientCore (z : G) : Subgroup G :=
  (localCore z).map (involutionCentralizer z).subtype

/-- The local hypotheses preceding I.4.7, for a specified involution. -/
structure HTypeAt [Finite G] (z : G) : Prop where
  involution : orderOf z = 2
  core_equiv : Nonempty (localCore z ≃* MinusExtraspecial.Model)
  quotient_equiv : Nonempty
    ((involutionCentralizer z ⧸ localCore z) ≃* alternatingGroup (Fin 5))
  not_weakly_closed : ¬ ∀ t ∈ ambientCore z, IsConj z t → t = z

/-- Existence of the involution required for `H(2, Ω₄⁻(2))`-type. -/
def HType (G : Type*) [Group G] [Finite G] : Prop := ∃ z : G, HTypeAt z

/-- Exactly one nonempty ambient conjugacy class of involutions. -/
def OneInvolutionClass (G : Type*) [Group G] : Prop :=
  ∃ a : G, orderOf a = 2 ∧ ∀ t : G, orderOf t = 2 → IsConj t a

/-- Exactly two nonempty ambient conjugacy classes of involutions. -/
def TwoInvolutionClasses (G : Type*) [Group G] : Prop :=
  ∃ a b : G, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b ∧
    ∀ t : G, orderOf t = 2 → IsConj t a ∨ IsConj t b

/-- The source's type `J₂`, without any simplicity assumption. -/
def J2Type (G : Type*) [Group G] [Finite G] : Prop :=
  HType G ∧ TwoInvolutionClasses G

/-- The source's type `J₃`, without any simplicity assumption. -/
def J3Type (G : Type*) [Group G] [Finite G] : Prop :=
  HType G ∧ OneInvolutionClass G

end CFSG.Quasithin.Janko23
