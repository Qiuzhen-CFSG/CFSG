module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.Representation.Quotient

/-!
# The literal action required in K.3.3

The matrix field has order `2^(2*s)`; the fixed field of the stored conjugation
has order `2^s`. A natural identification includes both a group equivalence
and binary coordinates intertwining the original column action. For a pulled
back SU action, quasiequivalence permits a group automorphism, accounting for
the dual and field twists in Guralnick--Malle's Table 7.

These are output specifications, not recognition assumptions in the source
hypotheses. The group-only covering input remains the existing central-quotient
contract; no faithfulness of its pullback is assumed.

Source: Aschbacher--Smith K.3.3, printed p.456; Guralnick--Malle,
*Classification of 2F-modules, II*, Theorem 4.10 and Table 7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
open BenderSuzuki.MatrixGroups

variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]

/-- A genuine natural-module identification on the original layer. -/
structure NaturalModel (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (J : HermitianForm 3 F) where
  groupEquiv : L ≃* J.specialSubgroup
  coordinates : V ≃ₗ[ZMod 2] (Fin 3 → F)
  intertwines : ∀ (g : L) (v : V),
    coordinates (ρ (g : G) v) =
      Matrix.mulVec (groupEquiv g).val.val (coordinates v)

/-- Quasiequivalence to the actual natural column action of SU, allowing
automorphisms but retaining the full special group. This predicate is an
output of the minimal-degree classifier, not an input to source recognition. -/
def IsNatural (J : HermitianForm 3 F)
    (σ : Representation (ZMod 2) J.specialSubgroup V) : Prop :=
  ∃ (a : J.specialSubgroup ≃* J.specialSubgroup)
    (E : V ≃ₗ[ZMod 2] (Fin 3 → F)),
    ∀ g v, E (σ g v) = Matrix.mulVec (a g).val.val (E v)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition
