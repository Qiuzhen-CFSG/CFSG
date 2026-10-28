module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Adequate
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.KernelGeometry
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
/-!
# Recovering the full component interface after E.6.22

If an ordinary component has action corank one, its full fixed subspace
is a hyperplane. Restricting the actual component to that hyperplane's
centralizer contradicts the characteristic-two conclusion of E.6.22.
Thus neither the linear-four nor the odd row survives, and the adequate
model output supplies the unchanged full interface for the later E.6.23
consumers. No kernel equality is assumed or inferred from corank alone.
Source: Aschbacher–Smith, E.6.22–23, printed pp.254–255.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- A characteristic-two hyperplane centralizer cannot contain this ordinary component. -/
theorem actionCorank_ne_one_of_hyperplane_characteristicTwo
    (hchar : ∀ W : Subgroup G, Hyperplanes.IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (hUV : U ≤ V) (hL : ComponentIn (centralizer (U : Set G)) L) :
    actionCorank V L ≠ 1 := by
  intro hc
  let W := V ⊓ centralizer (L : Set G)
  have hW : Hyperplanes.IsHyperplane V W := ⟨inf_le_left,hc⟩
  have hLW : ComponentIn (centralizer (W : Set G)) L :=
    RemainingSieve.OddActions.KernelGeometry.componentIn_intermediateCentralizer hL
      (fixedSpace_contains hUV hL.1) le_rfl
  have hcore : centralizer (pCore 2 (centralizer (W : Set G)) :
      Set (centralizer (W : Set G))) ≤ pCore 2 (centralizer (W : Set G)) := by
    rw [←hchar W hW]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  exact not_isComponent_of_twoCore hcore _ hLW.2

/-- E.6.22 eliminates exactly the rows whose kernel fields were not established. -/
theorem AdequateComponentAlternatives.full_of_hyperplane_characteristicTwo
    (ha : AdequateComponentAlternatives M V U Q L)
    (hchar : ∀ W : Subgroup G, Hyperplanes.IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (hUV : U ≤ V) (hL : ComponentIn (centralizer (U : Set G)) L) :
    ComponentAlternatives M V U Q L := by
  rcases ha with hb | hs | h4 | ha | ho
  · exact Or.inl hb
  · exact Or.inr (Or.inl hs)
  · exact (actionCorank_ne_one_of_hyperplane_characteristicTwo hchar hUV hL h4.2.2.1).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact (actionCorank_ne_one_of_hyperplane_characteristicTwo hchar hUV hL ho.2.1).elim
end CFSG.Quasithin.ChapterE.Section06.Components
