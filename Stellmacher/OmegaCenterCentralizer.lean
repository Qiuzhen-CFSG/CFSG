module
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PGroup.OmegaCenterDetection
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Detecting a Sylow centralizer in its omega center

When a finite two-group normalizes a subgroup, its centralizer of that
subgroup is normal in the two-group. A nontrivial such centralizer meets
its omega center. Thus vanishing on the omega center forces the whole
centralizer to vanish, including every Thompson-alpha fixed summand.

Source: the finite p-group center principle, applied in Aschbacher–Smith
10.2.3(4), printed p.746.
-/
public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of_omega_center
    (S H : Subgroup G) (hS : IsPGroup 2 S)
    (hSH : S ≤ normalizer (H : Set G))
    (hz : omegaOneCenterAmbient S ⊓ centralizer (H : Set G) = ⊥) :
    S ⊓ centralizer (H : Set G) = ⊥ := by
  apply eq_bot_of_normalized_of_omega_center_disjoint S _ hS inf_le_left
  · exact (le_inf S.le_normalizer
      (hSH.trans (normalizer_le_normalizer_centralizer H))).trans
        inf_normalizer_le_normalizer_inf
  · apply bot_unique
    apply le_trans (le_inf (inf_le_left.trans ?_) (inf_le_right.trans inf_le_right)) hz.le
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    obtain ⟨z,hz,rfl⟩ := hx
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨z.property,hx2,fun s hs => congrArg S.subtype
        ((mem_center_iff.mp hz) ⟨s,hs⟩)⟩
end Stellmacher
