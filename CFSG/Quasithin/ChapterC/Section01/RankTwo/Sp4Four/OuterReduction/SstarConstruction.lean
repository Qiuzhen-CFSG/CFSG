module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CharacteristicReduction
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Conjugation

/-!
# Literal Sylow seed for the characteristic replacement

The source seed in (3.4) uses the intersection of the original full Sylow
with the normal component. This module transports that intersection into the
actual characteristic overgroup. The replacement radical is not asserted to
map onto a Sylow; the source actor is retained separately. A surjective
component quotient sends the component Sylow to a genuine Sylow of the model.

Source: MS93 (3.0),(3.4), pp.859, 868. The construction preserves the
original Sylow witness and does not split the central attachment.
-/

public section
open Subgroup
open Representation
open Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {J K F : Type*} [Group J] [Finite J]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A Sylow subgroup of a normal component, obtained by intersecting a chosen
ambient Sylow. -/
noncomputable def componentSylow (L : Subgroup J) [L.Normal]
    (P : Sylow 2 J) : Sylow 2 L :=
  Classical.choose (Sylow.exists_subgroupOf_eq_of_subnormal P L
    (inferInstance : L.Normal).isSubnormal)

theorem componentSylow_coe (L : Subgroup J) [L.Normal]
    (P : Sylow 2 J) :
    (componentSylow L P : Subgroup L) = (P : Subgroup J).subgroupOf L := by
  exact Classical.choose_spec (Sylow.exists_subgroupOf_eq_of_subnormal P L
    (inferInstance : L.Normal).isSubnormal)

/-- The carrier of the source actor inside the characteristic overgroup. -/
noncomputable def sourceSylow
    {L R : Subgroup J} (d : CharacteristicReduction L R)
    [L.Normal] (P : Sylow 2 L) : Subgroup d.overgroup :=
  ((P : Subgroup L).map L.subtype).subgroupOf d.overgroup

omit [Finite J] in
/- The source actor is literally the component--Sylow intersection. -/
theorem sourceSylow_coe
    {L R : Subgroup J} (d : CharacteristicReduction L R)
    [L.Normal] (_hL : L ≤ d.overgroup) (P : Sylow 2 L) :
    (sourceSylow d P : Set d.overgroup) =
      ((P : Subgroup L).map L.subtype).subgroupOf d.overgroup := by
  rfl

/-- A surjective component quotient transports the source component Sylow to a
model Sylow. This is independent of the replacement radical image. -/
noncomputable def sourceModelSylow
    {L : Subgroup J} [L.Normal] (P : Sylow 2 L)
    (q : L →* Sp F) (hq : Function.Surjective q) : Sylow 2 (Sp F) :=
  P.mapSurjective (f := q) hq


omit [Algebra (ZMod 2) F] in
/- Every model Sylow has its literal fixed natural line, with the marking
 retained for later transport to the cover. -/
theorem modelSylow_fixedLine
    (S : Sylow 2 (Representation.SymplecticFourOrthogonalCover.L (K := F))) :
    ∃ g : Representation.SymplecticFourOrthogonalCover.L (K := F),
      fixed ((symplecticDerivedNatural 2).comp
        (S : Subgroup (Representation.SymplecticFourOrthogonalCover.L (K := F))).subtype) =
        Representation.SymplecticFourOrthogonalCover.SylowFlag.movedLine g := by
  obtain ⟨g, hg⟩ :=
    Representation.SymplecticFourOrthogonalCover.SylowFlag.exists_marking S
  refine ⟨g, ?_⟩
  rw [hg]
  exact Representation.SymplecticFourOrthogonalCover.SylowFlag.movedLine_fixed g

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem sourceModelSylow_coe
    {L : Subgroup J} [L.Normal] (P : Sylow 2 L)
    (q : L →* Sp F) (hq : Function.Surjective q) :
    (sourceModelSylow P q hq : Subgroup (Sp F)) =
      (P : Subgroup L).map q := by
  exact Sylow.coe_mapSurjective (f := q) hq P

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
