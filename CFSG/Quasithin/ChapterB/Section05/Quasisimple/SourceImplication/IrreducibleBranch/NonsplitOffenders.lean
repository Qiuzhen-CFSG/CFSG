module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Sieve
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.CoverReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Symplectic

/-!
# Offender containment in the final irreducible branch of B.5.1

The corrected full local catalogue and nonzero central attachment leave
only L3(2) and Sp4(2^n), n>1. In the first case faithful action on the binary
three-dimensional quotient forces T into L. In the second case the original
best offenders remain best on the literal moved space. The natural symplectic
normalizer calculation then puts them in L: quotienting cannot increase fixed
codimension, and the semilinear involution centralizer bound excludes outer
offenders, including its equality case. Source observation alpha gives G=L.

The original reduction, retaining the actual natural action and nontrivial
component covering, remains available. The final theorems complete this
nonsplit branch under its full corrected local catalogue premise. No further
earlier-source implication, ambient-fixed-kernel assertion, splitting or
outer-extension conclusion is assumed. The B.5.1 assembly owner supplies
the local catalogue through the complete corrected B.4.2 input.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1,
final irreducible-branch paragraph, printed p.100, citing I.2.3, p.413.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Complete the binary-three case and expose only the genuine symplectic cover case. -/
theorem nonsplit_small_ratio_reduction [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase
      (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)))
    (hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G)))
    (hz : s.central.toSubmodule ≠ ⊥)
    (hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) < 1) :
    ((∀ A ≤ (T : Subgroup G), IsBestOffender ρ A → A ≤ L) ∧ L = ⊤) ∨
      ∃ F : BinaryField, 1 < F.degree ∧
        Nonempty (ActionEquiv (s.action.comp L.subtype) (binarySymplectic F)) ∧
        quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) = 2 / 3 ∧
        IsCover (componentMovedProjection s (L ⊔ (T : Subgroup G))) ∧
        (componentMovedProjection s (L ⊔ (T : Subgroup G))).toLinearMap.ker ≠ ⊥ := by
  let := h.finite_module
  rcases nonsplit_small_ratio_natural h s hi T hc hJ hz hq with hn | ⟨F, hF, hn, hr⟩
  · exact Or.inl ⟨fun A hAT _ => hAT.trans (sylow_le_of_binaryThree h s T hn),
      whole_of_binaryThree h s T hn⟩
  · have hp := local_cover_data s hi T hz
    exact Or.inr ⟨F, hF, hn, hr, hp.1, hp.2.1⟩

/-- Every original best offender in T lies in L in the nonsplit, small-ratio branch. -/
theorem nonsplit_small_ratio_offenders_le [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase
      (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)))
    (hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G)))
    (hz : s.central.toSubmodule ≠ ⊥)
    (hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) < 1) :
    ∀ A ≤ (T : Subgroup G), IsBestOffender ρ A → A ≤ L := by
  let := h.finite_module
  rcases nonsplit_small_ratio_reduction h s hi T hc hJ hz hq with
    hd | ⟨F, hF, ⟨e⟩, _, _, _⟩
  · exact hd.1
  · intro A hAT hA
    exact symplectic_cover_bestOffender_le h s T F hF e A hAT
      (local_bestOffender_on_movedSpace s (hAT.trans le_sup_right) hA)

/-- Source alpha completes the final nonsplit, small-ratio irreducible branch. -/
theorem whole_of_nonsplit_small_ratio [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase
      (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)))
    (hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G)))
    (hz : s.central.toSubmodule ≠ ⊥)
    (hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) < 1) :
    L = ⊤ := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  apply whole_of_sylow_offenders_le ρ L T h.generated
  exact iSup₂_le fun A hA =>
    nonsplit_small_ratio_offenders_le h s hi T hc hJ hz hq A hA.2 hA.1

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
