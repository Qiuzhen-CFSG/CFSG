module

public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Index
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ComponentFusion

/-!
# Rudvalis involution-centralizer reductions

Global checked involution coverage reduces the full centralizer table to
independent calculations for max6 and the full centralizer of a. This module
assembles the exact successive-extension and Suzuki-product alternatives
conditionally on those two marked structures. Component exclusion in max6
must come from its actual kernel action; its abstract factor orders do not
supply it. Given that exclusion and the C(a) product, every possible component
is Sz(8), and its ambient Sylow centralizer index is strictly greater than two.

The marked structure inputs are not proved by these reductions. The final
source assembly remains open until both are discharged. The component-fusion
extension likewise retains the single concrete marked-kernel fusion witness.
Source: Aschbacher–Smith, 16.1.5(11), 16.1.7(3)(i), 16.1.8 and 16.3.4,
printed pp.1172–1173,1178; GLS3 Table 5.3r.
-/

@[expose] public section

open Subgroup
namespace Rudvalis.InvolutionCentralizers
open SylowOvergroups

/-- Global coverage reduces the full table to two independent marked structure calculations. -/
theorem centralizer_alternatives_of_marked
    (hfirst : FirstShape max6)
    (hsecond : Nonempty (Centralizer a ≃* Elementary 2 × SzEight))
    (t : Model) (ht : orderOf t = 2) :
    FirstShape (Centralizer t) ∨
      Nonempty (Centralizer t ≃* Elementary 2 × SzEight) := by
  rcases centralizer_representatives t ht with ⟨_, ⟨f⟩⟩ | ⟨_, ⟨f⟩⟩
  · exact Or.inl (hfirst.of_equiv f.symm)
  · exact Or.inr ⟨f.trans hsecond.some⟩

/-- The marked component exclusion and actual product isomorphism imply the component type and strict index bound for arbitrary involutions. -/
theorem component_data_of_marked
    (hfirst : ∀ D : Subgroup max6, ¬ Theory.GroupTheory.IsComponent max6 D)
    (hsecond : Nonempty (Centralizer a ≃* Elementary 2 × SzEight))
    (t : Model) (ht : orderOf t = 2) (D : Subgroup (Centralizer t))
    (hD : Theory.GroupTheory.IsComponent (Centralizer t) D) :
    Nonempty (D ≃* SzEight) ∧
      ∀ P : Sylow 2 Model, 2 < ((Centralizer t).subgroupOf P).index := by
  rcases centralizer_representatives t ht with ⟨_, ⟨f⟩⟩ | ⟨_, ⟨f⟩⟩
  · exact (hfirst _ (hD.map_equiv f)).elim
  · let e := f.trans hsecond.some
    exact ⟨⟨componentEquivSuzuki e D hD⟩, suzuki_centralizer_sylow_index t e⟩

end Rudvalis.InvolutionCentralizers
