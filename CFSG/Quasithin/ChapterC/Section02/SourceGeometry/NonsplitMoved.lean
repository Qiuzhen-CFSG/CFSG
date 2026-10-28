module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Nonzero fixed points in the actual C.2.7 moved module

A nonidentity ambient element in the star commutator and in C_G(K)
becomes a nonzero vector in both the moved and fixed spaces of the
literal star action. These spaces therefore cannot be complementary.
The proved B.5.1 theorem then gives Irr⁺ and its nonsplit natural list
on the actual central quotient of the moved section.

The generic conclusion packages the same action data before specializing
to the star quotient, avoiding repeated typeclass expansion through the
nested subgroup and quotient carriers. No resource limits are raised.
The original A₇ application supplies its fixed involution z.

Source: Aschbacher–Smith C.2.7 and B.5.1(2), used in Lemma 12.3.3,
printed p.808.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
/-- B.5.1 on an actual moved section whose nonzero fixed part prevents splitting. -/
structure NonsplitMovedConclusion
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D) where
  source : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C
  nonsplit : ¬ IsCompl source.sectionData.space.toSubmodule (fixedSpace ρ C)
  irrPlus : IsIrrPlus ρ C source.sectionData.space.toSubmodule
  natural : NonsplitNatural (source.sectionData.action.comp C.subtype)

variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- The original fixed element obstructs splitting and discharges the
nonsplitting premise of B.5.1(2) on the actual star action. -/
theorem star_moved_nonsplit_of_fixed_point
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {z : G} (hz1 : z ≠ 1)
    (hz : z ∈ (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map
      (K ⊔ R : Subgroup G).subtype ⊓ centralizer (K : Set G)) :
    let ρ := starRepresentation K R
    let J := offenderSubgroup ρ
    starImage K R K ≤ J ∧
    Nonempty (NonsplitMovedConclusion (ρ.comp J.subtype)
      ((starImage K R K).subgroupOf J)) := by
  let V := starV K R
  let C := K.subgroupOf (K ⊔ R)
  let q := QuotientGroup.mk' (starKernel K R)
  let ρ := starRepresentation K R
  let J := offenderSubgroup ρ
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  have hs : c.sectionData.space.toSubmodule =
      NormalElementaryQuotient.commutatorSpace V C := by
    rw [NormalElementaryQuotient.commutatorSpace_eq V q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),c.sectionData.space_eq]
    change subspaceCommutator (ρ.comp J.subtype) ⊤ ((starImage K R K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  obtain ⟨w,hw,hwz⟩ := hz.1
  let v : Additive V := Additive.ofMul ⟨w,commutator_le_left V C hw⟩
  have hvm : v ∈ c.sectionData.space.toSubmodule := by
    rw [hs]
    exact hw
  have hvf : v ∈ fixedSpace ρ (C.map q) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) C v).mpr
    intro k hk
    apply Subtype.ext
    change (k : G) * (w : G) = (w : G) * (k : G)
    change (w : G) = z at hwz
    rw [hwz]
    exact hz.2 k hk
  have hvf' : v ∈ fixedSpace (ρ.comp J.subtype) ((starImage K R K).subgroupOf J) := by
    intro k
    exact hvf ⟨k.val.val,k.property⟩
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (ρ.comp J.subtype) ((starImage K R K).subgroupOf J)) := by
    intro hc
    have hv0 : v = 0 := Submodule.disjoint_def.mp hc.disjoint v hvm hvf'
    apply hz1
    have hw1 := congrArg (fun a : Additive V => ((a.toMul : V) : (K ⊔ R : Subgroup G))) hv0
    exact hwz.symm.trans (congrArg Subtype.val hw1)
  exact ⟨hCJ,⟨⟨c,hn,(c.clause_two hn).1,(c.clause_two hn).2⟩⟩⟩

end CFSG.Quasithin.ChapterC.C27Source
