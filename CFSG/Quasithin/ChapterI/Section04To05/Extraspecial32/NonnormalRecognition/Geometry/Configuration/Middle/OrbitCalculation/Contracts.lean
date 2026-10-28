module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Interfaces
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Endpoints

/-!
# Local class-incidence contract for the middle fusion count

The remaining calculation is intrinsic to M = N_G(E): count the same
M-conjugacy class in A and in Q, in each case outside E. This makes no
assertion about ambient G-fusion. The separate four-point intersection
A ∩ E accounts for the three nonidentity elements already fused to z.

`FusionCount` proves that these local incidences imply the nine-point
ambient count once the source fusion union in Q is supplied. The matching
itself remains to be constructed in the split natural E₈ ⋊ SL₃(2) model.
Source: Aschbacher, “A 2-local characterization of M12”, Lemmas 2.6(3)
and 3.1, printed pp.35–37.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
variable {G : Type*} [Group G]

/-- All involutions in the actual core, including the central involution. -/
abbrev coreInvolutions (z : G) : Set G := {x | x ∈ coreInG z ∧ orderOf x = 2}

/-- Conjugation by the actual involution centralizer. -/
abbrev centralizerOrbit (z x : G) : Set G :=
  {t | ∃ c : Centralizer z, (c : G) * x * (c : G)⁻¹ = t}

/-- The literal endpoint normalizer. -/
abbrev endpointNormalizer (z g : G) := normalizer (coreIntersection z g : Set G)

/-- Involutions in the endpoint normalizer, outside its embedded kernel E. -/
abbrev normalizerInvolutionsOutside (z g : G) (B : Subgroup G) :
    Set (endpointNormalizer z g) :=
  {x | (x : G) ∈ B ∧ (x : G) ∉ coreIntersection z g ∧ orderOf (x : G) = 2}

/-- Intrinsic class incidence in M, independent of ambient fusion. This is
an output contract, whose construction is still a source obligation. -/
structure MiddleClassMatching (z g : G) (A : Subgroup G) : Prop where
  plane_card : Nat.card (A ⊓ coreIntersection z g : Subgroup G) = 4
  class_fibers : ∀ c : ConjClasses (endpointNormalizer z g),
    Nat.card {x : normalizerInvolutionsOutside z g A //
      ConjClasses.mk (x : endpointNormalizer z g) = c} =
    Nat.card {x : normalizerInvolutionsOutside z g (coreInG z) //
      ConjClasses.mk (x : endpointNormalizer z g) = c}

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
end
