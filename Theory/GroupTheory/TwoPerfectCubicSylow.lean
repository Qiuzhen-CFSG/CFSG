module

public import Theory.GroupTheory.TwoPerfectCubicImages
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Actual Sylow images in cubic two-perfect actions

A cubic quotient by the two-core kills every two-subgroup, so every full
Sylow two-subgroup is the two-core. Applying this to the actual range of
a homomorphism identifies the literal image of the original Sylow with
the embedded two-core of that range.

Source: the equality Aut_(T∩L₊)(P*) ≃ Q₈ in Aschbacher–Smith 13.3.14(d),
printed p.892. No Sylow-image or core-image equality is assumed.
-/

public section
open Subgroup

namespace Sylow

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem eq_twoCore_of_cubic_quotient (S : Sylow 2 A)
    (hthree : Nat.card (A ⧸ pCore 2 A) = 3) : (S : Subgroup A) = pCore 2 A := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have h3 : IsPGroup 3 (A ⧸ pCore 2 A) := IsPGroup.of_card (n := 1) hthree
  have hd := (S.isPGroup'.map q).disjoint_of_coprime (h3.to_subgroup ⊤) (by decide)
  have hz : (S : Subgroup A).map q = ⊥ := by simpa only [disjoint_top] using hd
  have hle : (S : Subgroup A) ≤ pCore 2 A := by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  exact le_antisymm hle (pCore_isPGroup.le_sylow_of_normal S)

theorem image_eq_embedded_twoCore_of_cubic_quotient
    {B : Type*} [Group B] [Finite B] (S : Sylow 2 A) (f : A →* B)
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (hm : (pCore 2 A).map f ≠ ⊥) :
    (S : Subgroup A).map f = (pCore 2 f.range).map f.range.subtype := by
  have hm' : (pCore 2 A).map f.rangeRestrict ≠ ⊥ := by
    intro hz
    apply hm
    have hh := congrArg (map f.range.subtype) hz
    rw [map_map, Subgroup.map_bot] at hh
    have he : f.range.subtype.comp f.rangeRestrict = f := by ext; rfl
    rwa [he] at hh
  have hcard := f.rangeRestrict.twoCore_quotient_card_three
    f.rangeRestrict_surjective hA hthree hm'
  have hh := (S.mapSurjective f.rangeRestrict_surjective).eq_twoCore_of_cubic_quotient hcard
  rw [coe_mapSurjective] at hh
  have he := congrArg (map f.range.subtype) hh
  rw [map_map] at he
  have hf : f.range.subtype.comp f.rangeRestrict = f := by ext; rfl
  rwa [hf] at he

end Sylow
