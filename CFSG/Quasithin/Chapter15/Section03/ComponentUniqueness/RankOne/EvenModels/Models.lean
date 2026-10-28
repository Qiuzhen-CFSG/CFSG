module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Configuration
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# The incoming characteristic-two alternatives

These definitions transcribe 1.1.5(3)(a)--(c) for use in 15.3.43.
Every family is tied to the component by a genuine model equivalence.
The rank-two list is exactly Theorem C's list, with its small derived
groups, genuine triality construction, and Ree field restrictions.
The unitary parameter is the fixed-field order. Suzuki is omitted here
because the preceding 15.3.34 branch has already excluded it.

The nontrivial central two-covers of PSL₃(4) and G₂(4) are retained.
The alternating-six alternative records the actual transposition action
on the central quotient and both possible centre orders, one and three.
Quasisimplicity and the two-group centre of the incoming component come
from `ReducedConfiguration`; thus the centre-three case must be excluded,
not silently identified with the simple component.

No parabolic classification, field restriction from the local geometry,
or centralizer conclusion is an input in these definitions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
1.1.5(3)(a)--(c), printed pp.501--502; A.2.3--4, p.33; 15.3.43, p.1140.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

universe u

/-- The simple families of C(3)--(4), after the separate Suzuki exclusion. -/
inductive SimpleModel (H : Type u) [Group H] (n : ℕ) : Prop
  | linearTwo (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL H 2 (2 ^ n))
  | unitaryThree (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSU H 3 (2 ^ n))
  | rankTwo (model : ChapterA.Section02.IsTheoremCRankTwoModel H n)
  | binaryLinear (hn : n = 1) (d : ℕ) (hd : d = 4 ∨ d = 5)
      (iso : ClassicalGroup.IsPSL H d 2)

variable {G : Type u} [Group G]

/-- Literal inner action on the original component, including its centre. -/
def ActsInner (L : Subgroup G) (z : G) : Prop :=
  ∃ l : L, ∀ x : L, z * (x : G) * z⁻¹ = (l : G) * (x : G) * (l : G)⁻¹

/-- A transposition on the actual central quotient, with conjugation
compatibility. The implication suffices because conjugation by the source
involution preserves the component. -/
def ActsTransposition (L : Subgroup G) (z : G) : Prop :=
  ∃ (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) (t : Equiv.Perm (Fin 6)),
    t.IsSwap ∧ ∀ x y : L, (y : G) = z * (x : G) * z⁻¹ →
      (e (QuotientGroup.mk' (center L) y) : Equiv.Perm (Fin 6)) =
        t * (e (QuotientGroup.mk' (center L) x) : Equiv.Perm (Fin 6)) * t⁻¹

/-- Precisely the three incoming source branches, retaining the source
involution action and the allowed central covers. -/
inductive Model (L : Subgroup G) (z : G) (n : ℕ) : Prop
  | simple (simple : IsSimpleGroup L) (model : SimpleModel L n)
      (inner : ActsInner L z)
  | linearThreeCover (hn : n = 2) (nontrivialCenter : center L ≠ ⊥)
      (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) (inner : ActsInner L z)
  | g2Cover (hn : n = 2) (nontrivialCenter : center L ≠ ⊥)
      (iso : ClassificationModels.IsG2At (L ⧸ center L) 4) (inner : ActsInner L z)
  | alternatingSix (hn : n = 1) (centerOrder : Nat.card (center L) = 1 ∨
      Nat.card (center L) = 3) (action : ActsTransposition L z)

/-- Genuine earlier involution data from 1.1.5. These are not conclusions
of the local parabolic inspection in 15.3.43. -/
structure SourceInvolution (S M : Subgroup G) (z : G) : Prop where
  order : orderOf z = 2
  mem : z ∈ S
  central : ∀ s ∈ S, s * z = z * s
  centralizer_le : centralizer ({z} : Set G) ≤ M

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
