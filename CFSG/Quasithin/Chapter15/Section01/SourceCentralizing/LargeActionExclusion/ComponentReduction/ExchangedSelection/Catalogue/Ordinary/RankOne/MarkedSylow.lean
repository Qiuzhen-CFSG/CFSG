module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary

/-!
# The original nontrivial involutory Sylow fixer

A nonidentity central involution of T acts faithfully on the selected ordinary
component and fixes its literal Sylow subgroup S_L pointwise. This retains
the same pre-exclusion component and its actual conjugation action. It is
used by the exceptional central-cover calculations, with no model premise.
Source: Aschbacher--Smith 15.1.20(3), first paragraph, p.1095.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Faithfulness supplies a nontrivial involution on the same original component. -/
theorem PreExclusionSource.exists_nontrivial_sylow_fixer
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ∃ P : Sylow 2 d.L, (P : Subgroup d.L).map d.L.subtype = d.SL ∧
      ∃ α : MulAut d.L, α^2=1 ∧ α≠1 ∧ ∀ x ∈ P, α x=x := by
  obtain ⟨z,hz,hzne⟩ := (Subgroup.bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  obtain ⟨R,hR,h115⟩ := d.ordinary_involution_inputs hG hu h s.centralizer_sylow
  have hzc : z ∈ centralizer (d.S : Set G) := by
    intro x hx
    exact (h115 z hz hzne).central x (hR.symm ▸ hx)
  have hz2 : z*z=1 := by
    simpa only [(h115 z hz hzne).involution,pow_two] using pow_orderOf_eq_one z
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (d.L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩:d.L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    have hzbot : z ∈ (⊥ : Subgroup G) := (s.ordinary hL).central_faithful ▸ ⟨hz,hc⟩
    exact hzne (mem_bot.mp hzbot)
  obtain ⟨P,hP⟩ := s.component_sylow
  refine ⟨P,hP,α,hα2,hαne,?_⟩
  intro x hx
  apply Subtype.ext
  rw [ha]
  exact mul_inv_eq_iff_eq_mul.mpr
    (hzc x (d.SL_le_S (hP ▸ mem_map_of_mem d.L.subtype hx))).symm



end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
