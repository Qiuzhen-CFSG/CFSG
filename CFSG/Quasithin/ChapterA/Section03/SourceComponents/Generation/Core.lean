module

public import Theory.GroupTheory.CComponent.GenerationByRadicalAction
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Mathlib.GroupTheory.IndexNormal
/-!
# The simple-section and orbit inputs to A.3.9(1)

The actual radical quotient of each component is nonabelian simple, hence
semisimple. Theorem A therefore gives strongly quasithinness on precisely
that section; the K-group hypothesis transports along its literal quotient
map. The proved orbit bound makes each original component normal under the
solvable residual. These inputs discharge the general action-kernel generation
argument, without any ordinary-cover classification.

Source: Aschbacher--Smith, A.3.9(1), printed p.46.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.GenerationCore
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

variable (hA : ∀ (X : Type u) [Group X] [Finite X],
    Section02.TheoremA κ X)


include hA in
/-- Theorem A applies to the actual nonabelian simple radical quotient of a component. -/
lemma radical_quotient_sqtk (hG : IsSQTK κ G)
    {L : Subgroup G} (hL : L.IsCComponent) :
    IsSQTK κ (L ⧸ solvableRadical L) := by
  let Q := L ⧸ solvableRadical L
  let := hL.perfect
  let := hL.isSimpleGroup_quotient_solvableRadical
  have hc : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (hL.not_isMulCommutative_quotient_solvableRadical
        (center_eq_top_iff.mp hc)).elim
  let : IsQuasisimple Q := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hsem : Section02.IsSemisimple Q := by
    apply top_unique
    exact le_sSup (show IsComponent Q ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsec : Section02.IsSectionOf Q G := .quotient_subgroup L _
  exact ⟨(hA G).stronglyQuasithin_section hG.stronglyQuasithin hG.isKGroup hsec hsem,
    hsec.isKGroup hG.isKGroup⟩

private lemma residual_le_component_normalizer (hG : IsSQTK κ G)
    (hO : pCore 2 G = ⊥) {L : Subgroup G} (hL : L.IsCComponent) :
    solvableResidual G ≤ normalizer (L : Set G) := by
  rcases ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (CComponentCommutation.noncentralStructureInput κ) hG hO hL
    with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · let N := normalizer (L : Set G)
    let : N.Normal := normal_of_index_eq_two hi
    let : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := 2) hi
    exact solvableResidual_le_of_solvable_quotient N

end CFSG.Quasithin.ChapterA.Section03.SourceComponents.GenerationCore

namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.GenerationCore
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- A.3.9(1), using the original ambient components and their radical quotient actions. -/
theorem generation
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA κ X)
    (hSimple : ∀ (S : Type u) [Group S] [Finite S],
      IsSimpleGroup S → ¬ IsMulCommutative S → IsSQTK κ S →
        Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S))
    (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥) :
    cComponentLayer G = solvableResidual G := by
  apply cComponentLayer_eq_residual_of_radical_actions
  · intro L hL
    exact residual_le_component_normalizer hG hO hL
  · intro B C hB hC hne
    exact CComponentCommutation.commutator_eq_bot hG hO hB hC hne
  · intro L hL
    exact (hSimple _ hL.isSimpleGroup_quotient_solvableRadical
      hL.not_isMulCommutative_quotient_solvableRadical
      (radical_quotient_sqtk hA (hG.subgroup (solvableResidual G)) hL)).1

end CFSG.Quasithin.ChapterA.Section03.SourceComponents.GenerationCore
