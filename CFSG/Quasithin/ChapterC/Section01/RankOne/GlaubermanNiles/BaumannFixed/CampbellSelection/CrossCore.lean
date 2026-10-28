module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.CoreEscape
/-!
# Cross-core placement for original marked natural subgroups

For two C.1.17 groups sharing the entire marked Baumann base, [B,V′] lies
in Ω₁(Z(B)), whose image belongs to F in every target. Thus a transported
V′ outside the target core forces [O²(H),O₂(H)] ≤ V by CoreEscape.
This supplies Campbell II.8's cross-core step directly for the original
family, avoiding the larger tilde-J embedding family used in the thesis.

Source: Campbell II.8, printed p.38; Aschbacher–Smith C.1.17–18.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H H' : Type*} [Group B] [Finite B] [Group H] [Finite H]
  [Group H'] [Finite H'] {e : B →* H} {e' : B →* H'}

theorem InLocalClass.transferred_V_core_commutator (h : InLocalClass e)
    (h' : InLocalClass e') (hB : IsBaumannFixed B) :
    ⁅((Campbell.V H').comap e').map e,pCore 2 H⁆ ≤ Campbell.F H := by
  obtain ⟨T,he,_⟩ := h.sylow
  have hQS : pCore 2 H ≤ e.range := he ▸ pCore_isPGroup.le_sylow_of_normal T
  apply (commutator_mono le_rfl hQS).trans
  rw [commutator_comm,MonoidHom.range_eq_map,←map_commutator]
  exact (map_mono (h'.campbell_seed_le_omegaCenter hB)).trans h.omegaCenter_map_le_F

theorem InLocalClass.transferred_V_core_or_residual_bound (h : InLocalClass e)
    (h' : InLocalClass e') (hB : IsBaumannFixed B) :
    ((Campbell.V H').comap e').map e ≤ pCore 2 H ∨
      ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H := by
  by_cases hv : ((Campbell.V H').comap e').map e ≤ pCore 2 H
  · exact Or.inl hv
  · exact Or.inr (h.residual_core_le_V_of_noncore_commutator hB _
      (map_le_range _ _) hv (h.transferred_V_core_commutator h' hB))

theorem InLocalClass.transferred_V_le_core_of_no_residual_bound (h : InLocalClass e)
    (h' : InLocalClass e') (hB : IsBaumannFixed B)
    (hn : ¬ ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H) :
    ((Campbell.V H').comap e').map e ≤ pCore 2 H :=
  (h.transferred_V_core_or_residual_bound h' hB).resolve_right hn

end CFSG.Quasithin.ChapterC.GlaubermanNiles
