module

public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation.Core
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import Theory.GroupTheory.CComponent.SylowContainment

/-!
# Source inputs to unique C-component containment

Generation supplies containment in the ambient component layer. Theorem A
and the simple SQTK parity input apply to the actual radical quotient of B
inside B sup T. The general full-Sylow containment theorem then applies
with all its hypotheses discharged by these earlier source results.

Source: Aschbacher--Smith, A.3.12, first assertion, printed pp.47--48.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.ContainmentCore
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The unique-containment assertion of A.3.12, before its proper-embedding cases. -/
theorem containment
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA κ X)
    (hSimple : ∀ (S : Type u) [Group S] [Finite S],
      IsSimpleGroup S → ¬ IsMulCommutative S → IsSQTK κ S →
        Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S))
    (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents T) :
    ∃! L : Subgroup G, L.IsCComponent ∧ B ≤ L := by
  let M := B ⊔ (T : Subgroup G)
  have hB₀ : (B.subgroupOf M).IsCComponent := hB
  let : Group.IsPerfect (B.subgroupOf M) := hB₀.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ M from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ M from le_sup_left)).surjective
  have hBH : B ≤ cComponentLayer G := by
    rw [GenerationCore.generation hA hSimple hG hO]
    exact le_solvableResidual_of_isPerfect B
  exact existsUnique_cComponent_of_local_of_le_layer T B hB hBH
    (hSimple _ hB₀.isSimpleGroup_quotient_solvableRadical
      hB₀.not_isMulCommutative_quotient_solvableRadical
      (GenerationCore.radical_quotient_sqtk hA (hG.subgroup M) hB₀)).2
    (fun C D hC hD hne => CComponentCommutation.commutator_eq_bot hG hO hC hD hne)

end CFSG.Quasithin.ChapterA.Section03.SourceComponents.ContainmentCore
