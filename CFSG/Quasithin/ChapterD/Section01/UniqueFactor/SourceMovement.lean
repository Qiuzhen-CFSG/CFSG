module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceThompson

/-!
# Thompson movement on the actual residual module

In the unique-chief-factor, centralizing-closure branch, the two-residual
acts nontrivially on its idempotent commutator module. The minimal-parabolic
kernel theorem therefore places its centralizer in the maximal core. If
J(O₂(G₁)) centralized this module, it would lie in O₂(G₂), contradicting
the original common-normal exclusion. The consumer is the selected
Chapter 3 residual-Sylow argument.
Source: Aschbacher--Smith D.1.4--5 and 3.1.6, pp.176--177,573--575.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ T V : Subgroup G}
/-- The Thompson subgroup of the first core moves the actual residual module. -/
theorem source_thompson_moves_residual_module
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    ¬ elementaryAbelianMaxJ (twoCoreIn G₁) ≤
      centralizer ((⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G) : Set G) := by
  let I := ⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆
  let R := twoCoreIn G₁
  let J := elementaryAbelianMaxJ R
  let f := actionHom G₂ I (residual_module_normalized d)
  have hRH : R ≤ G₂ := (left_core_le_sylow d).trans (sylow_le_right d)
  have hKHnot : ¬ pResidual 2 G₂ ≤ f.ker := by
    intro hk
    have hic : I ≤ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
      intro i hi r hr
      obtain ⟨r,hr,rfl⟩ := hr
      have hh := hk hr
      rw [actionHom_ker] at hh
      exact (hh i hi).symm
    exact residual_commutator_ne_bot d (module_ne_bot hu)
      ((residual_commutator_idempotent d hV).symm.trans
        (commutator_eq_bot_iff_le_centralizer.mpr hic))
  obtain ⟨S,hS⟩ := d.sylow_right
  have hP := intrinsic_minimalParabolic_of_coreClosure_centralizes d (module_ne_bot hu) hc S hS
  have hker : f.ker ≤ ChapterB.minimalParabolicCore S hP :=
    ChapterB.minimalParabolic_normal_le_core_of_residual_not_le S hP f.ker hKHnot
  have hJR : J ≤ R := sSup_le fun _ hA => hA.1
  intro hj
  apply source_thompson_core_not_le_right_core d (module_ne_bot hu) hc
  intro j hjJ
  let jH : G₂ := ⟨j,hRH (hJR hjJ)⟩
  have hjS : jH ∈ S := by
    have ht := (left_core_le_sylow d) (hJR hjJ)
    rw [← hS] at ht
    obtain ⟨s,hs,he⟩ := ht
    change G₂.subtype s = G₂.subtype jH at he
    exact G₂.subtype_injective he ▸ hs
  have hjC : jH ∈ f.ker := by
    rw [actionHom_ker]
    exact hj hjJ
  have hjcore : jH ∈ pCore 2 G₂ := by
    rw [← ChapterB.minimalParabolic_sylow_inf_core S hP]
    exact ⟨hjS,hker hjC⟩
  exact mem_map_of_mem G₂.subtype hjcore
end CFSG.Quasithin.ChapterD.UniqueFactor
