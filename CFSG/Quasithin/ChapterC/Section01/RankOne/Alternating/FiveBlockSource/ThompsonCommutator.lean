module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.MarkedSource
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.ElementaryThompsonFrattini
/-!
# Thompson commutator generation of the original component

The actual Thompson four-group acts nontrivially on the self-centralizing
simple A₅ image. Two-perfectness lifts full commutator generation through
the original two-group kernel. The external two-group is retained using
the intermediate-subgroup equality of the Thompson subgroups.
Source: C.1.21(1–2), C.1.23(1), printed pp.128–130.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB Theory.SpecificGroups.SymmetricFive
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The marked Thompson image acts nontrivially on the actual simple A₅
layer; two-perfectness lifts full commutator generation through the kernel. -/
theorem component_eq_thompson_commutator
    (R : Subgroup H) (L : Subgroup H) [L.Normal] (hp : IsPPerfect 2 L)
    (q : H →* Equiv.Perm (Fin 5)) (hk : IsPGroup 2 q.ker)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hJ : (elementaryAbelianMaxJ R).map q = OuterFourGeometry.four) :
    L = ⁅L,elementaryAbelianMaxJ R⁆ := by
  apply eq_commutator_of_isPPerfect_of_map_eq L _ hp le_normalizer_of_normal q hk
  rw [hL,hJ]
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact SimpleSocle.commutator_eq _
    (GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide))
    OuterFourGeometry.four (by
      intro h
      have hc := OuterFourGeometry.four_card
      rw [h] at hc
      simp at hc)

/-- The same conclusion uses the original external two-group's J. -/
theorem component_eq_external_thompson_commutator
    (T R L : Subgroup H) [L.Normal] (hp : IsPPerfect 2 L)
    (hBR : baumann T ≤ R) (hRT : R ≤ T)
    (q : H →* Equiv.Perm (Fin 5)) (hk : IsPGroup 2 q.ker)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hJ : (elementaryAbelianMaxJ R).map q = OuterFourGeometry.four) :
    L = ⁅L,elementaryAbelianMaxJ T⁆ := by
  rw [←elementaryAbelianMaxJ_eq_of_intermediate T R
    ((elementaryAbelianMaxJ_le_baumann T).trans hBR) hRT]
  exact component_eq_thompson_commutator R L hp q hk hL hJ

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
