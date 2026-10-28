module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.Nilpotent

/-!
# Residual supplements from normal generation

A normally generating subgroup covers the quotient by the prime residual.
Otherwise its image lies in a maximal subgroup of that finite p-group;
normality of the maximal subgroup contradicts normal generation. This
argument does not require the original generator to be Sylow.

Source application: the replacement action in DGS, Groups and Graphs
(1985), 6.4, pp.120--121.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- A subgroup normally generating the group covers every finite p-group quotient. -/
theorem pResidual_sup_eq_top_of_normalClosure {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) (hA : normalClosure (A : Set G) = ⊤) :
    pResidual p G ⊔ A = ⊤ := by
  let q := QuotientGroup.mk' (pResidual p G)
  have him : A.map q = ⊤ := by
    by_contra hn
    obtain ⟨M,hM,hAM⟩ := (eq_top_or_exists_le_coatom (A.map q)).resolve_left hn
    let : Group.IsNilpotent (G ⧸ pResidual p G) := (isPGroup_quotient_pResidual p).isNilpotent
    let : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
      Group.normalizerCondition_of_isNilpotent hM
    have ht : (⊤ : Subgroup G) ≤ M.comap q := by
      rw [←hA]
      exact normalClosure_le_normal (map_le_iff_le_comap.mp hAM)
    apply hM.ne_top
    apply top_unique
    intro x _
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pResidual p G) x
    exact ht (mem_top g)
  have hh := congrArg (Subgroup.comap q) him
  simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top,sup_comm] using hh
end Subgroup
