module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.FusionAssembly
public import Theory.GroupTheory.BalancedConjugateCentralizers

/-!
# The balanced-centralizer endgame for the original binary G₂ row

The model calculation gives equal mutual action indices and identifies the
commutator with the fixed subgroup. These identities identify both mutual
centralizers with the original intersection. The conjugate fixed involution
therefore lies in V, so source fusion forces the conjugator into N_G(V).
This discharges the separate commutator-symmetry input of the earlier consumer.

Source: Aschbacher--Smith 12.4.9, printed p.816. The normalizer inclusion and
model identities remain explicit inputs of their independent producers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The original commutator obstruction from the two literal model identities,
without a separate fixed-line or conjugation-symmetry premise. -/
theorem lemma_12_4_9_of_balanced_g2_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (g : G)
    (hindex : (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V =
      (centralizer (V : Set G)).relIndex (V.map (MulAut.conj g).toMonoidHom))
    (hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ =
      V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcommne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  obtain ⟨z, _, hzgen, hcent, hweak, _⟩ :=
    source_g2_fusion h D structural e hne hNT
  have hz : z ∈ V := (show z ∈ fixedSubgroup L V from hzgen ▸ mem_zpowers z).1
  have hfixed : z ∈ centralizer (L : Set G) :=
    (show z ∈ fixedSubgroup L V from hzgen ▸ mem_zpowers z).2
  have hN : normalizer (V : Set G) = centralizer ({z} : Set G) := by
    obtain ⟨z₀, _, hz₀gen, hM, hMV, _, _⟩ :=
      exists_fixed_involution_setup h D structural e hne
    have hNV : normalizer (V : Set G) ≤ normalizer (L : Set G) := hMV.symm.le
    apply le_antisymm _ hcent
    intro m hm
    have hfix := mem_centralizer_singleton_iff.mp (hM.le (hNV hm))
    have hz₀ : z ∈ zpowers z₀ := by
      rw [← hz₀gen]
      exact ⟨hz,hfixed⟩
    have hc : zpowers z₀ ≤ centralizer ({m} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hfix.symm)
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hc hz₀)).symm
  intro hVA
  have he := conjugate_eq_of_weakly_closed_mark_and_balanced_indices V hz hN
    hweak hindex hcomm hVA
  apply hcommne
  rw [he]
  exact commutator_self_eq_bot_iff.mpr inferInstance
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
