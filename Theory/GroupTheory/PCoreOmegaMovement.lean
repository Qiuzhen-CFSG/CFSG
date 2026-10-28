module
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import Stellmacher.OmegaOneCenterMap
/-!
# Moving a central two-core module into a normal subgroup

Suppose I normalizes C and U, and U lies in Ω₁Z(O₂(I)). If C generates U
by commutators, then U lies in C and hence in O₂(C). Since O₂(C) lies in
O₂(I), U remains central there. Thus U lies in [Ω₁Z(O₂(C)), C].

Source application: Aschbacher--Smith 14.6.10(5), printed p.1029, moving
the actual source plane into the selected component's central module.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G]

theorem moved_omegaCenter_le_core_commutator (I C U : Subgroup G)
    (hCI : C ≤ I) (hIC : I ≤ normalizer (C : Set G))
    (hIU : I ≤ normalizer (U : Set G))
    (hU : U ≤ omegaOneCenterAmbient (I.pCoreIn 2)) (hm : ⁅U,C⁆ = U) :
    U ≤ ⁅omegaOneCenterAmbient (C.pCoreIn 2),C⁆ := by
  have hUI : U ≤ I := fun x hx =>
    pCoreIn_le 2 I ((mem_omegaOneCenterAmbient_iff _ x).mp (hU hx)).1
  have hUC : U ≤ C := hm ▸ le_normalizer_iff_commutator_le_right.mp (hUI.trans hIC)
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (I.pCoreIn 2)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 _).to_le hU
  have hUQ : U ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes hp hUC (hCI.trans hIU)
  have hCQ : C.pCoreIn 2 ≤ I.pCoreIn 2 := pCoreIn_mono_of_normalizes hCI hIC
  have hUΩ : U ≤ omegaOneCenterAmbient (C.pCoreIn 2) := by
    intro x hx
    obtain ⟨_,h2,hc⟩ := (mem_omegaOneCenterAmbient_iff _ x).mp (hU hx)
    exact (mem_omegaOneCenterAmbient_iff _ x).mpr ⟨hUQ hx,h2,fun q hq => hc q (hCQ hq)⟩
  exact hm ▸ commutator_mono hUΩ le_rfl

end Subgroup
