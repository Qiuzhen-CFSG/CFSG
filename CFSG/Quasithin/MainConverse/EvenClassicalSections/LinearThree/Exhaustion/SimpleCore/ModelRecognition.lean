module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.SimpleCore.Reduction
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.SimpleCore.ModelRecognition.RootGroups

/-!
# Elation generation for the simple core

A nonidentity elation in the simple core normally generates it. The large-root
condition supplies such an element through the actual inclusion of the core
into PSL₃. Thus the remaining recognition problem concerns the group generated
by conjugates of concrete matrices, rather than an unattached family label.

The intrinsic recognition of the large-root and complementary configurations
is not proved here. The requested `coreModel_of_simple_normal_selfCentralizing`
theorem remains to be assembled once both recognition arguments are proved.
No K-group hypothesis or subgroup-classification assumption is used below.

Source: Hartley, Ann. Math. 27 (1925), 140–158, Theorem 1 and condition B;
GLS3, Theorem 6.5.3(e–i), `refs/KGroup/GLS3/chapter6.tex`.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open scoped MatrixGroups
open ModelRecognition

private theorem simple_normalClosure_singleton_eq_top {G : Type*} [Group G]
    [IsSimpleGroup G] (x : G) (hx : x ≠ 1) :
    Subgroup.normalClosure ({x} : Set G) = ⊤ := by
  rcases (inferInstance : (Subgroup.normalClosure ({x} : Set G)).Normal).eq_bot_or_eq_top
      with h | h
  · have hm := Subgroup.subset_normalClosure (show x ∈ ({x} : Set G) from rfl)
    rw [h] at hm
    exact (hx hm).elim
  · exact h

/-- A concrete nonzero root element in the core normally generates that core.
The normal closure is taken inside `N`, not in `U` or in PSL₃. -/
public theorem normalClosure_core_elation_eq_top
    (F : Type) [Field F] (U : Subgroup PSL(3,F))
    (N : Subgroup U) [IsSimpleGroup N] (g : PSL(3,F)) (a : F) (ha : a ≠ 0)
    (hm : elationHom F g (Multiplicative.ofAdd a) ∈ N.map U.subtype) :
    ∃ x : N, (U.subtype.comp N.subtype) x = elationHom F g (Multiplicative.ofAdd a) ∧
      Subgroup.normalClosure ({x} : Set N) = ⊤ := by
  obtain ⟨n, hn, he⟩ := hm
  let x : N := ⟨n, hn⟩
  have hx : x ≠ 1 := by
    intro hx
    apply (elationHom_ne_one_iff F g a).mpr ha
    calc
      elationHom F g (Multiplicative.ofAdd a) = (U.subtype.comp N.subtype) x := he.symm
      _ = 1 := by rw [hx, map_one]
  exact ⟨x, he, simple_normalClosure_singleton_eq_top x hx⟩

/-- The large-root branch has an explicit elation normal generator for the core. -/
public theorem exists_normal_generating_elation_of_thick_root
    (F : Type) [Field F] (U : Subgroup PSL(3,F))
    (N : Subgroup U) [IsSimpleGroup N]
    (hroot : HasThickElationRoot F (N.map U.subtype)) :
    ∃ (g : PSL(3,F)) (a : F) (x : N), a ≠ 0 ∧
      (U.subtype.comp N.subtype) x = elationHom F g (Multiplicative.ofAdd a) ∧
      Subgroup.normalClosure ({x} : Set N) = ⊤ := by
  obtain ⟨g, a, _, ha, _, _, hm, _⟩ := hroot
  obtain ⟨x, hx, hgen⟩ := normalClosure_core_elation_eq_top F U N g a ha hm
  exact ⟨g, a, x, ha, hx, hgen⟩

end CFSG.Quasithin.MainConverse.LinearThreeSections
