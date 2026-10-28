module

public import CFSG.KnownSimple.ConstructedSporadicCarriers
public import CFSG.KnownSimple.FischerCarrierContribution
public import CFSG.KnownSimple.LeechCarrierContribution
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier
public import Mathlib.Data.Fintype.Defs

/-!
# The twenty-six sporadic carriers

Each name below denotes a fixed, independently constructed group. The fifteen
original entries, seven Leech-related ATLAS representations and three Fischer
ATLAS representations are reused without changing their carriers. The final
entry is the automorphism group of the exact Griess forms on the fixed real
196884-dimensional space. In particular its Leech comparison and extraspecial
spin action are instantiated, not parameters of this catalogue.

The Fischer entry is Fi₂₄′, not Fi₂₄; O'N is projective, not 3.O'N; Co₁
and Suz use representations of the simple groups, not their central covers.
The Baby Monster presentation includes the two central-killing relations.
The imported contributions retain the source generator data, action conventions
and attribution. Alternate lattice constructions require proved comparison
isomorphisms before their properties can be transferred to these carriers.

Membership is an actual multiplicative equivalence, and transport composes
equivalences. No order or simplicity certificate is an input to the list.
Sources: Aschbacher, *Sporadic Groups*, the sporadic list and Sections 27–28
for the Griess algebra; the ATLAS references in the imported contributions;
Aschbacher–Smith, *The Classification of Quasithin Groups*, §0.1, for K.
-/

@[expose] public section

namespace CFSG.KnownSimple

universe u v

/-- All twenty-six sporadic simple-group names. -/
inductive SporadicName
  | m11 | m12 | m22 | m23 | m24
  | j1 | j2 | j3 | j4
  | hs | mcl | he | ru | suz | onan
  | co1 | co2 | co3
  | fi22 | fi23 | fi24Prime
  | hn | ly | th | babyMonster | monster
  deriving DecidableEq

instance : Fintype SporadicName where
  elems := { .m11, .m12, .m22, .m23, .m24, .j1, .j2, .j3, .j4,
    .hs, .mcl, .he, .ru, .suz, .onan, .co1, .co2, .co3,
    .fi22, .fi23, .fi24Prime, .hn, .ly, .th, .babyMonster, .monster }
  complete := by intro name; cases name <;> simp

theorem sporadicName_card : Fintype.card SporadicName = 26 := by decide

/-- The sourced group corresponding to each sporadic name. -/
def SporadicName.Carrier : SporadicName → Type
  | .m11 => Sporadic.Mathieu.M11
  | .m12 => Sporadic.Mathieu.M12
  | .m22 => Sporadic.Mathieu.M22
  | .m23 => Sporadic.Mathieu.M23
  | .m24 => Sporadic.Mathieu.M24
  | .j1 => Janko1.Model
  | .j2 => Sporadic.LeechRelated.J2.Carrier
  | .j3 => Sporadic.Janko3.Model
  | .j4 => Janko4.Model
  | .hs => Sporadic.LeechRelated.HS.Carrier
  | .mcl => Sporadic.LeechRelated.McL.Carrier
  | .he => Held.He
  | .ru => Rudvalis.Model
  | .suz => Sporadic.LeechRelated.Suz.Carrier
  | .onan => ONan.Model
  | .co1 => Sporadic.LeechRelated.Co1.Carrier
  | .co2 => Sporadic.LeechRelated.Co2.Carrier
  | .co3 => Sporadic.LeechRelated.Co3.Carrier
  | .fi22 => Sporadic.Fischer.Fi22.Carrier
  | .fi23 => Sporadic.Fischer.Fi23.Carrier
  | .fi24Prime => Sporadic.Fischer.Fi24Prime.Carrier
  | .hn => HaradaNorton.HN
  | .ly => Lyons.LyonsGroup
  | .th => Thompson.Model
  | .babyMonster => BabyMonster.Carrier
  | .monster => Sporadic.Monster.GriessGroup

noncomputable instance SporadicName.carrierGroup (name : SporadicName) :
    Group name.Carrier := by
  cases name <;> unfold SporadicName.Carrier <;> infer_instance

/-- Isomorphism to one of the twenty-six fixed sporadic carriers. -/
def IsSporadicCarrier (G : Type u) [Group G] : Prop :=
  ∃ name : SporadicName, Nonempty (G ≃* name.Carrier)

theorem isSporadicCarrier_carrier (name : SporadicName) :
    IsSporadicCarrier name.Carrier := ⟨name, ⟨MulEquiv.refl _⟩⟩

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsSporadicCarrier.of_mulEquiv (h : IsSporadicCarrier G) (e : H ≃* G) :
    IsSporadicCarrier H := by
  obtain ⟨name, ⟨f⟩⟩ := h
  exact ⟨name, ⟨e.trans f⟩⟩

theorem isSporadicCarrier_mulEquiv_iff (e : G ≃* H) :
    IsSporadicCarrier G ↔ IsSporadicCarrier H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- The original fifteen entries embed with their original group structures. -/
theorem IsConstructedSporadicCarrier.isSporadicCarrier
    (h : IsConstructedSporadicCarrier G) : IsSporadicCarrier G := by
  obtain ⟨name, iso⟩ := h
  cases name with
  | m11 => exact ⟨.m11, iso⟩
  | m12 => exact ⟨.m12, iso⟩
  | m22 => exact ⟨.m22, iso⟩
  | m23 => exact ⟨.m23, iso⟩
  | m24 => exact ⟨.m24, iso⟩
  | j1 => exact ⟨.j1, iso⟩
  | j3 => exact ⟨.j3, iso⟩
  | j4 => exact ⟨.j4, iso⟩
  | he => exact ⟨.he, iso⟩
  | ru => exact ⟨.ru, iso⟩
  | hn => exact ⟨.hn, iso⟩
  | ly => exact ⟨.ly, iso⟩
  | th => exact ⟨.th, iso⟩
  | onan => exact ⟨.onan, iso⟩
  | babyMonster => exact ⟨.babyMonster, iso⟩

theorem IsLeechSporadicCarrier.isSporadicCarrier
    (h : IsLeechSporadicCarrier G) : IsSporadicCarrier G := by
  obtain ⟨name, iso⟩ := h
  cases name with
  | j2 => exact ⟨.j2, iso⟩
  | hs => exact ⟨.hs, iso⟩
  | co1 => exact ⟨.co1, iso⟩
  | co2 => exact ⟨.co2, iso⟩
  | co3 => exact ⟨.co3, iso⟩
  | mcl => exact ⟨.mcl, iso⟩
  | suz => exact ⟨.suz, iso⟩

theorem IsFischerSporadicCarrier.isSporadicCarrier
    (h : IsFischerSporadicCarrier G) : IsSporadicCarrier G := by
  obtain ⟨name, iso⟩ := h
  cases name with
  | fi22 => exact ⟨.fi22, iso⟩
  | fi23 => exact ⟨.fi23, iso⟩
  | fi24Prime => exact ⟨.fi24Prime, iso⟩

/-- The last entry is the fixed source Griess automorphism group. -/
theorem isSporadicCarrier_monster : IsSporadicCarrier Sporadic.Monster.GriessGroup :=
  ⟨.monster, ⟨MulEquiv.refl _⟩⟩

end CFSG.KnownSimple
