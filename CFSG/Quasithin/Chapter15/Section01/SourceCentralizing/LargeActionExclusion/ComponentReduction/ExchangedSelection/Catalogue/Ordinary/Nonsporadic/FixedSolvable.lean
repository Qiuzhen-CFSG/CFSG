module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Components
public import Theory.GroupAction.SylowFixedSolvable

/-!
# Solvability of the original local intersection from its marked fixed group

The empty faithful local family makes the solvable residual of M_c
centralize Z. The faithful marked action on L is a nonidentity involution
fixing S_L pointwise. Thus the solvable residual of M_L embeds in its
fixed group. If that fixed group is solvable, so is M_L.

The actual PSL₃ family supplies this model premise in HigherField.Linear,
including the retained perfect central two-covers. No exchanged component
or noncentral plane is used. Final catalogue assembly stays with
qt-e-15122-ordinary-pre-exclusion and qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 14.1.6 and 15.1.20, printed pp.977,1094--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Solvable fixed groups of the actual Sylow-central involutions force the
original local intersection to be solvable. -/
theorem PreExclusionSource.local_solvable_of_sylow_fixed_solvable
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hf : ∀ (P : Sylow 2 d.L) (a : MulAut d.L), orderOf a = 2 →
      (∀ x ∈ P, a x = x) → Group.IsSolvable a.fixedSubgroup) :
    Group.IsSolvable d.ML := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  obtain ⟨P,hP⟩ := s.component_sylow
  have hfix : ∀ x ∈ P, α x = x := by
    intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (centralInvolutions_le_centralizer_sylow T hz x
        (d.SL_le_S.trans d.S_le_T (hP ▸ mem_map_of_mem d.L.subtype hx))).symm
  have hz2 : z*z=1 := by
    have hh := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    simpa only [pow_two] using hh.2.1
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
      have hh := ha (⟨x,hx⟩ : d.L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact hzne (mem_bot.mp ((s.ordinary hL).central_faithful ▸ ⟨hz,hc⟩))
  let : Group.IsSolvable α.fixedSubgroup := hf P α (orderOf_eq_prime hα2 hαne) hfix
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro x hx
    exact hMc.2 (fun w hw => (centralInvolutions_le_centralizer_sylow T hw x hx).symm)
  have hres := residual_le_centralizer_Z
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,hTMc⟩
  let j : d.ML →* Mc := inclusion (show d.ML ≤ Mc from inf_le_left.trans inf_le_right)
  let f : solvableResidual d.ML →* α.fixedSubgroup := {
    toFun x := ⟨⟨x.val.val,x.val.property.2⟩,by
      rw [MulAut.mem_fixedSubgroup]
      apply Subtype.ext
      rw [ha]
      have hc := hres (mem_map_of_mem Mc.subtype
        (map_solvableResidual_le j (mem_map_of_mem j x.property))) z hz
      exact mul_inv_eq_iff_eq_mul.mpr hc⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun a : α.fixedSubgroup => ((a : d.L) : G)) hxy))
  let : Group.IsSolvable (solvableResidual d.ML) :=
    Group.isSolvable_of_isSolvable_injective hinj
  exact (Group.isSolvable_iff_subgroup_quotient (solvableResidual d.ML)).mpr
    ⟨inferInstance,inferInstance⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
