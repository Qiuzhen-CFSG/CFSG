module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Alternating
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.PerfectSymmetricNormal

/-!
# B.5.13 in the complementary outer symmetric case

Clause B.5.1(4b) makes the moved space the natural S₆ or S₈ module.
Its complement to the component-fixed space makes the central denominator
zero, so the moved quotient has the same action. The genuine quasisimple
component is perfect, nontrivial and normal; its image in Sₙ is therefore Aₙ.
The alternating moved-space estimate applies directly, including when the
original dual has nonzero central summands.

Source: Aschbacher–Smith, B.5.1(4b) and B.5.13, printed pp.99 and 111.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem central_eq_bot (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) : s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact (disjoint_iff.mp hc.disjoint).le ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩

private noncomputable def sectionNaturalEquiv {n : ℕ} (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (e : ActionEquiv s.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin n))) :
    ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin n)) where
  groupEquiv := e.groupEquiv
  linearEquiv := (s.central.toSubmodule.quotEquivOfEqBot (central_eq_bot s hc)).trans e.linearEquiv
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact e.intertwines g v

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem component_marking [L.Normal] [Group.IsPerfect L] [Nontrivial L]
    {n : ℕ} (hn : 5 ≤ n)
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n))) :
    L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n) := by
  let : (L.map e.groupEquiv.toMonoidHom).Normal :=
    (inferInstance : L.Normal).map e.groupEquiv.toMonoidHom e.groupEquiv.surjective
  let : Group.IsPerfect (L.map e.groupEquiv.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := (e.groupEquiv.subgroupMap L).toMonoidHom)
      (e.groupEquiv.subgroupMap L).surjective
  let : Nontrivial (L.map e.groupEquiv.toMonoidHom) :=
    (e.groupEquiv.subgroupMap L).injective.nontrivial
  exact Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simpa using hn) _

private noncomputable def alternatingRestriction {n : ℕ}
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n)))
    (hm : L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n)) :
    ActionEquiv (ρ.comp L.subtype) (alternatingNatural n) where
  groupEquiv := (e.groupEquiv.subgroupMap L).trans (MulEquiv.subgroupCongr hm)
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines g v

/-- The complementary natural S₆/S₈ branch, before inserting the B.5.1 source
conclusion. The bound is for the original representation, with arbitrary central summands. -/
theorem quadraticRatio_le_two_of_outer_symmetric_moved [L.Normal]
    (hq : IsQuasisimple L) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (s : MovedSection ρ.dual L)
    (hi : IsIrrPlus ρ.dual L s.space.toSubmodule)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ.dual L))
    (hnat : IsSymmetricNatural (D := G) (V := s.space.toSubmodule) s.space.toRepresentation n)
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let : Group.IsPerfect L := hq.toIsPerfect
  let : IsSimpleGroup (L ⧸ center L) := hq.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨en⟩ := hnat
  let e := sectionNaturalEquiv s hc en
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> decide
  have hm := component_marking (L := L) hn5 e
  have hindex : L.index = 2 := by
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [← Subgroup.index_map_equiv L e.groupEquiv]
    change (L.map e.groupEquiv.toMonoidHom).index = 2
    rw [hm]
    exact alternatingGroup.index_eq_two
  exact quadraticRatio_le_two_of_alternating_moved hn s hi
    ⟨alternatingRestriction e hm⟩ hindex.le hff

/-- B.5.13 in the outer complementary exception B.5.1(4b), on the literal dual.
The genuine quasisimple component supplies the alternating marking and index two. -/
theorem quadraticRatio_le_two_of_outer_symmetric_source
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hq : IsQuasisimple (generalizedFitting G))
    (hcL : IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (hnG : ¬ IsCompl c.sectionData.space.toSubmodule ρ.dual.invariants)
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let : L.Normal := c.fitting_eq ▸ inferInstance
  have hqL : IsQuasisimple L := c.fitting_eq ▸ hq
  obtain ⟨hi, hcases⟩ := c.clause_four hnG
  rcases hcases with hns | ⟨_, hnat, _⟩
  · exact False.elim (hns hcL)
  · rcases hnat with h6 | h8
    · exact quadraticRatio_le_two_of_outer_symmetric_moved hqL (Or.inl rfl)
        c.sectionData hi hcL h6 hff
    · exact quadraticRatio_le_two_of_outer_symmetric_moved hqL (Or.inr rfl)
        c.sectionData hi hcL h8 hff

end CFSG.Quasithin.ChapterB.SourceB513
