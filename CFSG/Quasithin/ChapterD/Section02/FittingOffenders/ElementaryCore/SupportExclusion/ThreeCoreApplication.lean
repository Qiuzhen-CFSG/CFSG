module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion
public import Theory.PGroupCore

/-!
# Support exclusion for the actual three-core

Apply the central-line exclusion to the literal subgroup O₃(G), retaining
the original representation, ambient centralizers, and Frattini inclusion.
The only preceding-source module premise is `HyperplaneSupport`.

Source: Aschbacher--Smith D.2.14(2), printed p.186, paragraph (++).
-/

public section
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open Subgroup Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every invariant central order-three line of the actual three-core is
excluded from its Frattini subgroup by the preceding hyperplane supports. -/
theorem threeCore_central_line_not_le_frattini (hρ : Function.Injective ρ)
    (A Z : Subgroup G) (hA : Nat.card A = 4)
    (hcentral : Z ≤ (center (pCore 3 G)).map (pCore 3 G).subtype)
    (hZ : Nat.card Z = 3) (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ (pCore 3 G) A) :
    ¬ Z ≤ (frattini (pCore 3 G)).map (pCore 3 G).subtype :=
  central_line_not_le_frattini ρ hρ (pCore 3 G) A Z pCore_isPGroup
    hA hcentral hZ hnZ hfix hs

end CFSG.Quasithin.ChapterD.ElementaryCore
