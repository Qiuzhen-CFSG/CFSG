module

public import CFSG.Quasithin.ChapterF.Section07.Geometry
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon

/-!
# Local actor contracts for the original quintic path action

The even prefixes require local order-four images at their quintic endpoint;
the odd prefixes require escape from the cubic endpoint kernel. Both retain
the same quintic root and the literal pointwise path stabilizer. The preceding
length's transitivity is an induction hypothesis. These predicates assert no
source existence theorem and have no ambient finiteness requirement.

The separate input module permits the two source families to be developed
independently and subsequently imported by the eight-path assembly.
Source: Aschbacher--Smith F.3.2--4, p.270; 14.2.20--21, pp.988--989.
-/

public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open ChapterF.Section07 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- Local four-cycle witnesses at the quintic endpoints of even paths.
Only prefix transitivity is available when constructing the next actor. -/
@[expose] def QuinticEvenExtensionActors (X H : Subgroup G) : Prop :=
  let F := Geometry.family X H
  ∀ n, 2 ≤ n → n < 8 → Even n →
    RootPathTransitive (graph F) (X ⊔ H : Subgroup G) (base F true) n →
    ∀ p : BasedWalk (graph F) n (base F true), p.Nonbacktracking →
      ∃ a ∈ pathStabilizer F p,
        a ^ 4 ∈ ballKernel F p.endpoint 1 ∧ a ^ 2 ∉ ballKernel F p.endpoint 1

/-- A pointwise fixer escapes the local kernel at the cubic endpoint of each
odd path. The root is still the quintic vertex. -/
@[expose] def QuinticOddExtensionEscape (X H : Subgroup G) : Prop :=
  let F := Geometry.family X H
  ∀ n, 2 ≤ n → n < 8 → Odd n →
    RootPathTransitive (graph F) (X ⊔ H : Subgroup G) (base F true) n →
    ∀ p : BasedWalk (graph F) n (base F true), p.Nonbacktracking →
      ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
