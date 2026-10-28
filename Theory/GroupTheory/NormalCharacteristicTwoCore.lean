module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Nontrivial normal subgroups in characteristic two

If C_G(O₂(G))≤O₂(G), every nontrivial normal subgroup N has nontrivial
two-core. Otherwise N∩O₂(G)=1; normality makes N centralize O₂(G),
forcing N into that same trivial intersection.

This is the nontrivial-core step in the exclusion of the product amalgam
in Aschbacher–Smith13.4.9, printed p.906. No finiteness hypothesis is needed.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
theorem twoCore_ne_bot_of_normal_of_centralizer_le (N : Subgroup G) [N.Normal]
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) (hne : N ≠ ⊥) :
    pCore 2 N ≠ ⊥ := by
  intro hb
  have hi : N ⊓ pCore 2 G ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
    (pCore_isPGroup.to_le inf_le_right) inf_le_left le_normalizer_of_normal
  have hz : N.pCoreIn 2 = ⊥ := by simp only [pCoreIn,hb,Subgroup.map_bot]
  have hc : N ≤ centralizer (pCore 2 G : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
      ((commutator_le_inf N (pCore 2 G)).trans (hz ▸ hi)))
  exact hne (le_bot_iff.mp ((le_inf le_rfl (hc.trans hG)).trans (hz ▸ hi)))


end Subgroup
