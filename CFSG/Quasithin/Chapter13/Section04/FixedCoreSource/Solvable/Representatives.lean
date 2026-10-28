module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Products
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.InvolutionRepresentatives
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Recognition from the source marked chamber

The invariant-Lagrangian argument supplies a representative of every
involution in the literal plane core. We restrict the original ambient
Sylow subgroup to E and transport the result through the actual third
vertex and its core map. Together with the commuting-product calculation,
this discharges both intrinsic involution premises in the existing
Burnside-fusion and characteristic-two recognition argument.

The final theorem still takes the marked chamber, the relative normality
of J(T), and the literal 13.4.7 overgroup supplement. Construction of the
local product and chamber remains with this solvable-branch owner; earlier
source inputs retain their producers and final discharge with
qt-d-1341-fixed-core-source. The four individual orbit identifications are
separate remaining exports of the consolidated task.

Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Every actual local involution has a representative in the ambient image of the plane core. -/
theorem original_plane_core_representative (D : ChosenModule T L V)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (a : G) (ha : a ∈ generated (normalizer (L : Set G)) z H₀)
    (hai : BenderSuzuki.PFAppendixIII.IsInvolution a) :
    ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
      MulAut.conj c a ∈ H₀.pCoreIn 2 := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hTE : (T : Subgroup G) ≤ E :=
    D.sylow_normalizes_component.trans (first_le_generated _ _ _)
  obtain ⟨c, hc⟩ := square_one_representative C.system (T.subtype hTE)
    C.chamber.symm (⟨a, ha⟩ : E) (Subtype.ext hai.2)
  change MulAut.conj c (⟨a, ha⟩ : E) ∈ (C.system.family 2).pCoreIn 2 at hc
  rw [C.third, pCoreIn_subgroupOf 2 H₀ E le_sup_right] at hc
  exact ⟨c.val, c.property, hc⟩

open scoped Pointwise in
/-- The marked chamber discharges both intrinsic involution inputs to recognition. -/
theorem isPSp_of_source_marked_chamber
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement : ∀ X : Subgroup G, X ∈ Chapter1.HOver G (H₀ : Set G) →
      (X : Set G) = (H₀ : Set G) *
        (X ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  apply isPSp_of_source_thompson_representatives h₀ h structural D m z H₀ C hnormal supplement
  exact original_plane_core_representative D z H₀ C
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
