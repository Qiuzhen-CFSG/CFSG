module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Interfaces
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Endpoints

/-!
# Local data for the elementary sixteen in source Lemma 3.1

These are properties of the split point normalizer and its Sylow two-subgroup:
the middle elementary sixteen, its centralizer and normalizer inside H, its
uniqueness inside the chosen Sylow subgroup, and the Sylow center. This is a
local construction contract; no ambient fusion or normalizer quotient is assumed.

`Control` uses uniqueness and Sylow conjugacy to prove control of the fusion
of z into A. The existence of this local data remains a separate obligation.
Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), proof of Lemma 3.1, printed p.36.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] {z : G}

/-- A Sylow subgroup of H embedded along the literal inclusion into G. -/
abbrev middleSylowImage (S : Sylow 2 (Centralizer z)) : Subgroup G :=
  (S : Subgroup (Centralizer z)).map (Centralizer z).subtype

/-- The conjugates of z lying in the proposed middle subgroup. -/
abbrev MiddleFusion (z : G) (A : Subgroup G) := {x : G // x ∈ A ∧ IsConj z x}

/-- Outside the two endpoint eights, the core involutions form one H-orbit.
This is the precise part of source 2.3(2)(a) needed for the fusion exclusion. -/
def ThirdCoreOrbit (z g y : G) : Prop :=
  ∀ x ∈ coreInG z, orderOf x = 2 →
    x ∉ coreIntersection z g → x ∉ coreIntersection z y →
    ∀ t ∈ coreInG z, orderOf t = 2 →
      t ∈ coreIntersection z g ∨ t ∈ coreIntersection z y ∨
        ∃ c : Centralizer z, (c : G) * x * (c : G)⁻¹ = t

/-- Local Sylow geometry to be constructed in the split point normalizer.
The square condition gives the elementary four quotient T/A; uniqueness
provides the fusion argument without assuming a Thompson-subgroup theorem. -/
structure MiddleLocalData (z : G) where
  A : Subgroup G
  elementary : IsElementaryAbelian 2 A
  card : Nat.card A = 16
  S : Sylow 2 (Centralizer z)
  A_le_sylow : A ≤ middleSylowImage S
  sylow_square : ∀ t ∈ middleSylowImage S, t ^ 2 ∈ A
  relative_centralizer : Centralizer z ⊓ centralizer (A : Set G) = A
  normalizer_intersection : Centralizer z ⊓ normalizer (A : Set G) = middleSylowImage S
  unique_sixteen : ∀ B : Subgroup G, B ≤ middleSylowImage S →
    IsElementaryAbelian 2 B → Nat.card B = 16 → B = A
  sylow_center : (center (middleSylowImage S)).map (middleSylowImage S).subtype = zpowers z


end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
