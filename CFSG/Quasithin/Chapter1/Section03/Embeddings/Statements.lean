module

public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.ClassicalModels
public import Theory.Mathieu.M11.Basic
public import CFSG.Quasithin.Defs

/-!
# The four embedding alternatives in Proposition 1.3.4

These are the conclusions, not additional hypotheses on a member of Ξ.
All models use actual group isomorphisms. The swapped case records an internal
direct product of the two specified conjugate intersections. The automizer is
the image of the actual conjugation action of N_T(P) on P.

The intrinsic input below collects precisely the local conclusions of 1.3.2
used on printed pp. 509–511. In particular it does not require T to be Sylow
in the overgroup. The source explicitly permits this use on printed p. 1052.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 1.3.4, pp. 509–511.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The concrete elementary abelian group E_(p²). -/
abbrev Plane (p : ℕ) := Multiplicative (Fin 2 → ZMod p)

/-- Aut_T(P) means the automorphisms induced by N_T(P), even when T does not normalize P. -/
def automizer (T P : Subgroup G) : Subgroup (MulAut P) :=
  (P.normalizerMonoidHom.comp (inclusion (show T ⊓ normalizer P ≤ normalizer P from
    inf_le_right))).range

/-- The exact internal conjugate factorization in 1.3.4(1). -/
def SwappedFactors (T P L₀ : Subgroup G) : Prop :=
  ¬ T ≤ normalizer L₀ ∧ ∃ t : G,
    t ∈ T ⊓ normalizer P ∧ t ∉ normalizer L₀ ∧
    P = (P ⊓ L₀) ⊔ (P ⊓ L₀).conjBy t ∧
    Disjoint (P ⊓ L₀) ((P ⊓ L₀).conjBy t) ∧
    ⁅P ⊓ L₀, (P ⊓ L₀).conjBy t⁆ = ⊥

/-- The two actual rank-one models allowed by 1.3.4(1). -/
def SwappedModel (p : ℕ) (Q : Type u) [Group Q] : Prop :=
  (∃ n : ℕ, Even n ∧ Nat.ModEq p (2 ^ n) 1 ∧ ClassicalGroup.IsPSL Q 2 (2 ^ n)) ∨
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL Q 2 q

/-- Both covers denoted `(S)L₃(p)` by the source; no unitary alternative is present. -/
def LinearThreeModel (p : ℕ) (Q : Type u) [Group Q] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) F)) ∨ ClassicalGroup.IsPSL Q 3 p

/-- Sp₄(2ⁿ), with the full symplectic carrier and both source parameter restrictions. -/
def SymplecticModel (p : ℕ) (Q : Type u) [Group Q] : Prop :=
  ∃ n : ℕ, Even n ∧ Nat.ModEq p (2 ^ n) 1 ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (Q ≃* Matrix.symplecticGroup (Fin 2) F)

/-- Precisely M₁₁, L₄(2), or L₅(2). -/
def ExceptionalModel (Q : Type u) [Group Q] : Prop :=
  Nonempty (Q ≃* Sporadic.Mathieu.M11) ∨
    ClassicalGroup.IsPSL Q 4 2 ∨ ClassicalGroup.IsPSL Q 5 2

/-- All four alternatives, sharing their actual E_(p²) isomorphism. -/
def Alternatives (p : ℕ) (T P L₀ : Subgroup G) : Prop :=
  Nonempty (P ≃* Plane p) ∧
    ((SwappedFactors T P L₀ ∧ SwappedModel p (XiQuotient L₀)) ∨
      (T ≤ normalizer L₀ ∧
        (LinearThreeModel p (XiQuotient L₀) ∨
          (SymplecticModel p (XiQuotient L₀) ∧ IsCyclic (automizer T P)) ∨
          (p = 3 ∧ ExceptionalModel (XiQuotient L₀)))))

/-- The genuine conclusion of 1.3.4, retaining relative normality in H. -/
def Conclusion (p : ℕ) (T X P H₀ : Subgroup G) : Prop :=
  (X.subgroupOf H₀).Normal ∨ ∃ L₀ : Subgroup G,
    L₀ ∈ cComponentsIn H₀ ∧ IsQuasisimple (XiQuotient L₀) ∧
      X ≤ componentOrbit L₀ T ∧ Alternatives p T P L₀

/-- Local witnesses from 1.3.2. The two-residual identity replaces any
unstated Sylow assumption on the overgroup H. -/
structure LocalInput (p : ℕ) (T X P H₀ : Subgroup G) : Prop where
  prime : p.Prime
  odd : Odd p
  overgroup : X ⊔ T ≤ H₀
  two_group : IsPGroup 2 T
  invariant : T ≤ normalizer X
  perfect : IsPPerfect 2 X
  quotient : XiOddQuotient p (XiQuotient X)
  sylow : IsSylowIn p P X
  complement : X.pCoreIn 2 ⊔ P = X
  disjoint : Disjoint (X.pCoreIn 2) P
  generation : closure {g : G | ∃ n ∈ X.pCoreIn 2, ∃ a ∈ P,
    n * a * n⁻¹ = g} = X
  core_commutator : X.pCoreIn 2 = ⁅X.pCoreIn 2, P⁆
  normalizer_factor : T = X.pCoreIn 2 ⊔ (T ⊓ normalizer P)
  irreducible : ∀ A : Subgroup (P ⧸ frattini P),
    (∀ s : (T ⊓ normalizer P : Subgroup G), ∀ a ∈ A,
      frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s a ∈ A) →
    A = ⊥ ∨ A = ⊤
  frattini_commutator : P = ⁅P, (frattini (T ⊓ normalizer P : Subgroup G)).map
    (T ⊓ normalizer P).subtype⁆
  residual : (pResidual 2 (H₀.pCoreIn 2 ⊔ X : Subgroup G)).map
    (H₀.pCoreIn 2 ⊔ X).subtype = X

end CFSG.Quasithin.Chapter1.XiEmbedding
