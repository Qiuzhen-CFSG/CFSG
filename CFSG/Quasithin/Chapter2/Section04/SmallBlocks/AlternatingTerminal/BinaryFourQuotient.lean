module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The binary-four quotient obstruction

An alternating-five block whose two-core dies in a two-kernel quotient
PSL₄(2) maps to an ordinary A₅. Full-Sylow local components descend through
the solvable kernel; the binary-four non-enlargement theorem then forces
A₅ to equal PSL₄(2), contrary to their orders.

Source: Aschbacher–Smith 2.4.25, printed p.543, the binary-five endpoint
parabolic in the final model inspection.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
variable {G : Type*} [Group G] [Finite G]

private theorem alternating_quasisimple (n : ℕ) (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp; omega))).trans QuotientGroup.quotientBot).isSimpleGroup

/-- An actual alternating-five block cannot be local for a full Sylow
in a two-group extension of PSL₄(2) when its two-core dies in that quotient. -/
theorem not_local_of_binary_four_quotient
    (q : G →* PSL(4, ZMod 2)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A : Subgroup G)
    (hA : ChapterC.IsAlternatingBlock A 5)
    (hcore : (pCore 2 A).map A.subtype ≤ q.ker) (S : Sylow 2 G) :
    A ∉ ChapterA.Section03.localCComponents S := by
  intro hlocal
  let := hk.isNilpotent
  let f := q.subgroupMap A
  have heker : f.ker = pCore 2 A := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance,?_⟩
      change IsPGroup 2 (q.subgroupMap A).ker
      rw [Subgroup.ker_subgroupMap]
      exact hk.comap_subtype
    · intro a ha
      apply Subtype.ext
      exact hcore (mem_map_of_mem A.subtype ha)
  let e := (QuotientGroup.quotientMulEquivOfEq heker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective A))
  obtain ⟨a⟩ := hA.2.2.quotient_iso
  let aA : A.map q ≃* alternatingGroup (Fin 5) := e.symm.trans a
  let := alternating_quasisimple 5 (by decide)
  let : IsQuasisimple (A.map q) := IsQuasisimple.of_mulEquiv aA.symm
  let ea := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  let := alternating_quasisimple 8 (by decide)
  let : IsQuasisimple PSL(4, ZMod 2) := IsQuasisimple.of_mulEquiv ea.symm
  let : IsQuasisimple (⊤ : Subgroup PSL(4, ZMod 2)) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : (⊤ : Subgroup PSL(4, ZMod 2)).IsCComponent :=
    IsComponent.isCComponent ⟨IsSubnormal.top,inferInstance⟩
  let Q := S.mapSurjective hq
  have hl : A.map q ∈ ChapterA.Section03.localCComponents Q :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal q
  have hm : ClassicalGroup.IsPSL (⊤ : Subgroup PSL(4, ZMod 2)) 4 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨topEquiv⟩⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_binary_linear_four_or_five Q
    hl ht le_top (Or.inl rfl) hm
  have hc : Nat.card (A.map q) = 60 := by
    rw [Nat.card_congr aA.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hcG : Nat.card PSL(4, ZMod 2) = 20160 := by
    rw [Nat.card_congr ea.toEquiv,nat_card_alternatingGroup]
    norm_num
  rw [he,card_top,hcG] at hc
  norm_num at hc
end CFSG.Quasithin.Chapter2.AlternatingTerminal
