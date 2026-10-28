module

public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections

/-!
# Compatibility with the existing homogeneous-section consumer

The lower-layer A.1.40 interface and the existing Chapter 15 interface use
the same original fixed-space quotient, orbit span, and equivariant linear
maps. This bridge preserves the full homogeneous-component equality.
The selection theorems below construct that existing consumer predicate,
either inside a seed's orbit span or from a faithful perfect actor.

Source: Aschbacher–Smith, A.1.40–42, printed pp.31–32.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions

namespace CFSG.Quasithin.ChapterA

/-- The Theory and existing Chapter 15 predicates have identical mathematical
content, including the literal central-image homogeneous equality. -/
theorem isIrrPlusWith_iff_chapter15 {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (X T : Subgroup G) (I : Submodule (ZMod 2) V) :
    Homogeneous.IsIrrPlusWith ρ X T I ↔ Cases.IsIrrPlusWith ρ X T I := by
  constructor <;> intro h
  · exact ⟨h.normalizes, h.invariant, h.isIrrPlus, h.homogeneous⟩
  · exact ⟨h.normalizes, h.invariant, h.isIrrPlus, h.homogeneous⟩

/-- A.1.42 selection with the exact homogeneous predicate used by Chapter 15. -/
theorem exists_chapter15_isIrrPlusWith_le_orbitSpan
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {X T : Subgroup G} (hT : T ≤ Subgroup.normalizer X) (hP : IsPGroup 2 T)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    ∃ J : Submodule (ZMod 2) V,
      J ≤ Cases.orbitSpan ρ T I ∧ Cases.IsIrrPlusWith ρ X T J := by
  obtain ⟨J, hJ, hh⟩ := Homogeneous.exists_isIrrPlusWith_le_orbitSpan ρ hT hP hI
  exact ⟨J, hJ, (isIrrPlusWith_iff_chapter15 ρ X T J).mp hh⟩

/-- A faithful nontrivial perfect actor supplies the homogeneous constituent
required by the existing FF-section consumers. -/
theorem exists_chapter15_isIrrPlusWith_of_faithful
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) (X T : Subgroup G) [Group.IsPerfect X]
    (hX : X ≠ ⊥) (hT : T ≤ Subgroup.normalizer X) (hP : IsPGroup 2 T) :
    ∃ I : Submodule (ZMod 2) V, Cases.IsIrrPlusWith ρ X T I := by
  obtain ⟨I, hI⟩ := Homogeneous.exists_isIrrPlusWith_of_faithful ρ hfaith X T hX hT hP
  exact ⟨I, (isIrrPlusWith_iff_chapter15 ρ X T I).mp hI⟩

end CFSG.Quasithin.ChapterA
