module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.MarkedParabolic
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionTransport
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.NormalTransport
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34

/-!
# The terminal point-parabolic comparison in §13.8

These theorems prove the final contradiction from the order conclusions of
13.8.34 and the strict containment from 13.8.11(1), once the source action
and its point stabilizer have been identified. The action comparison is an
explicit equivariant equivalence; an abstract four-dimensional vector-space
isomorphism does not suffice. The transporter `h` is retained in the statement.

The intrinsic calculation gives a normal subgroup of order at least eight,
contradicting the order-at-most-four consequence of 13.8.34(3). This avoids
identifying the point-parabolic residual with the other marked parabolic.
`marked_conjugate_contradiction` separately proves the containment route
when the precise residual marking is supplied.

`NormalTransport` strengthens that route: relative normality of the marked
subgroup suffices, since the strict normal extension contains the whole
point-parabolic two-core. Its action comparison uses an equivariant embedding
of the duad orbit, allowing the distinguished orbit inside the cover module.
It retains separate point and γ-to-α conjugators and requires neither a
preassigned A₄ image nor the desired marked containment.

`lemma_13_8_34` from `ActionAnalysis34` now proves
all conclusions of 13.8.34 from the explicit earlier local and marked-module
inputs. These comparison theorems retain their order hypotheses. The proof
of 13.8.33 and the discharge of the earlier source inputs remain assembly
obligations; no claim to Theorem 13.8.1 is made here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §13.8, printed pp. 966–969 (PDF pp. 983–986).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame

open Subgroup Theory.SpecificGroups.SymmetricSix

/-- The S₆ terminal contradiction with an equivariant identification of the
nonzero points of the natural module. For the cover alternative, applying
this requires the earlier identification of the relevant point stabilizer. -/
theorem s6_point_contradiction {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* S6) (f : X ≃ BinaryPoint)
    (heq : ∀ g x, f (g • x) = e g • f x) (x : X)
    (h : S6) (hx : h • (0 : Duad) = duadPolarEquiv.symm (f x))
    (U V : Subgroup G) (hVP : V ≤ MulAction.stabilizer G x)
    (hUn : MulAction.stabilizer G x ≤ normalizer (U : Set G))
    (hVn : MulAction.stabilizer G x ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) (hV : Nat.card V ≤ 4) : False := by
  apply no_small_relative_normal_pair (MulAction.stabilizer G x) U V _ hVP hUn hVn hU hlt hV
  exact Or.inr ⟨(stabilizerModel e f heq x).trans (polarPointModel (f x) h hx)⟩

/-- The A₆ terminal contradiction under the separately specified natural
action. No outer twist is inferred from the underlying carrier. -/
theorem a6_point_contradiction {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* A6) (f : X ≃ BinaryPoint)
    (heq : ∀ g x, f (g • x) = e g • f x) (x : X)
    (h : A6) (hx : h • (0 : Duad) = duadPolarEquiv.symm (f x))
    (U V : Subgroup G) (hVP : V ≤ MulAction.stabilizer G x)
    (hUn : MulAction.stabilizer G x ≤ normalizer (U : Set G))
    (hVn : MulAction.stabilizer G x ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) (hV : Nat.card V ≤ 4) : False := by
  apply no_small_relative_normal_pair (MulAction.stabilizer G x) U V _ hVP hUn hVn hU hlt hV
  exact Or.inl ⟨(stabilizerModel e f heq x).trans (evenPolarPointModel (f x) h hx)⟩

end CFSG.Quasithin.Chapter13.Section08.A6Endgame
