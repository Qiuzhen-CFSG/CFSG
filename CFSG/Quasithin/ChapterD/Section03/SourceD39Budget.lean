module

public import CFSG.Quasithin.ChapterD.Section03.Basic
public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.BinaryOffender.FlagCodimension

/-!
# The numerical D.3.9 bridge

The printed D.3.9 argument first turns every faithful chief section into the
two-rank datum `q̂ = codim / offenderRank`, then sums those data along a
chief flag.  This file supplies only that numerical bridge.  It does not
choose chief factors, assert an FF module, or identify a component model;
those source inputs remain explicit at the higher D.3 consumers.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.Section03

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- Convert an actual elementary actor and its fixed-codimension estimate into
the literal profile used by the D.3 chief-factor arithmetic. -/
public noncomputable def qhatProfileOf
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) : QHatProfile where
  offenderRank := rank A
  codim := fixedCodim ρ A
  offender_pos := hA.rank_pos
  bound := hbound

@[simp] public theorem qhatProfileOf_offenderRank
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    (qhatProfileOf ρ A hA hbound).offenderRank = rank A := rfl

@[simp] public theorem qhatProfileOf_codim
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    (qhatProfileOf ρ A hA hbound).codim = fixedCodim ρ A := rfl

theorem qhatProfileOf_value_le_two
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    (qhatProfileOf ρ A hA hbound).value ≤ 2 :=
  (qhatProfileOf ρ A hA hbound).value_le_two

end CFSG.Quasithin.ChapterD.Section03
