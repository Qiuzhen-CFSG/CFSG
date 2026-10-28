module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements

/-!
# Module interfaces for the outer-involution argument

`NaturalHead` records the actual natural section Q/H_C in J.2.2(3), with
the same H/Q marking as Ru2. Its existence is an earlier-source obligation.
`FreeAt` says that the fixed space of an involution equals its displacement
space. `OuterActionData` specifies the two freeness calculations and the
nontrivial action on C_Q(B)/Z used in J.2.5–6. These are proof obligations,
not additional assumptions in the definition of a group of type Ru.

Source: Aschbacher–Smith, J.2.2(3), J.2.5–6, printed pp.432, 434–435
(PDF pp.443, 445–446 of `refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The literal natural quotient Q/H_C, not just its dimension. -/
structure NaturalHead (d : TypeRuSetup G) where
  action : L2FourAction
  sectionData : BinaryConjugationSection d.H d.Q d.HC
    (action.action.comp d.ru2.quotientMap)

/-- Freeness on a binary module, expressed by fixed vectors and displacements. -/
def FreeAt {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) S5 W) (t : S5) : Prop :=
  ∀ v : W, ρ t v = v → ∃ w : W, ρ t w + w = v

/-- The module calculations still required by the outer lifting argument. -/
structure OuterActionData (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Prop where
  natural_free : ∀ i : d.H, (i : G) ∉ d.K → orderOf (i : G) = 2 →
    FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i)
  six_free : ∀ i : d.H, (i : G) ∉ d.K → orderOf (i : G) = 2 →
    FreeAt d.ru2.sixAction (d.ru2.quotientMap i)
  quaternion_moved : ∀ i : CB d B, (i : G) ∉ d.K → orderOf (i : G) = 2 →
    ∃ q ∈ HB d B, (i : G) * q * (i : G)⁻¹ * q⁻¹ ∉ d.Z

end CFSG.Quasithin.ChapterJ.Fusion.Outer
