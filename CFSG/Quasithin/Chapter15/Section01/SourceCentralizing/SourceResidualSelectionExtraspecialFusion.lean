module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialPartnerPlane
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.CentralizerFusion

/-!
# The remaining extraspecial fusion occurs inside the moved-plane centralizer

The actual partner module is U=[V,J₁(T)]. Source ordering factors its
central-seed centralizer through M and C_G(U). The M-factor already
normalizes E=C_V(J₁(T)), so the original residual duty is exactly
normalization of E by C_G(U). Failure supplies two actual conjugate
fixed four-spaces sharing the same literal moved plane, with the
conjugating element centralizing that plane.

This is a reduction of the remaining source duty, not its discharge.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The surviving global residual duty is exactly normalization by the
centralizer of the literal original moved plane. -/
theorem PreparedChosenModule.extraspecial_residual_iff_moved_centralizer_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G) ↔
    centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) ≤
      normalizer (thompsonFixed T V : Set G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  have hseed := (h.extraspecial_thompson_moved_seed_and_card hG T hempty hM hmany hJ hfull hex).1
  have hmod := (h.extraspecial_partner_module_and_normalizer hG T hempty hM hmany hJ hu hfull hex).1
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc ⟨hMcC.1,hTMc⟩
  rw [h.thompsonFixed_residual_iff_normalizes hG T hM hJ]
  constructor
  · intro hn
    exact (centralizer_le hseed).trans hn
  · intro hn g hg
    obtain ⟨a,ha,c,hc,he⟩ := hord g (hMcC.2 hg)
    have hcU : c ∈ centralizer (U : Set G) := by
      change c ∈ centralizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G)
      rw [←hmod]
      exact hc.2
    have hcZ : c ∈ centralizer (centralInvolutions T : Set G) := centralizer_le hseed hcU
    have haZ : a ∈ centralizer (centralInvolutions T : Set G) := by
      have hh := (centralizer (centralInvolutions T : Set G)).mul_mem hg
        ((centralizer (centralInvolutions T : Set G)).inv_mem hcZ)
      rw [←he,mul_inv_cancel_right] at hh
      exact hh
    rw [←he]
    exact (normalizer (thompsonFixed T V : Set G)).mul_mem
      (h.seedCentralizer_normalizes_thompsonFixed T hM ⟨ha.2,haZ⟩) (hn hcU)

/-- A failure gives an actual crossed conjugate pair inside C_G(U),
sharing U, whose second member is not normalized by the original J(T). -/
theorem PreparedChosenModule.extraspecial_failure_crossed_fixed_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let E := thompsonFixed T V
    ∃ g ∈ centralizer (U : Set G),
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (E.map (MulAut.conj g).toMonoidHom : Set G) ∧
      U ≤ E ⊓ E.map (MulAut.conj g).toMonoidHom ∧
      E ⊔ E.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  classical
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  have hn : ¬ centralizer (U : Set G) ≤ normalizer (E : Set G) :=
    mt (h.extraspecial_residual_iff_moved_centralizer_normalizes
      hG T hempty hM hmany hJ hu hfull hex).mpr hnot
  obtain ⟨g,hg,hgne⟩ := Set.not_subset.mp hn
  have hseed := (h.extraspecial_thompson_moved_seed_and_card hG T hempty hM hmany hJ hfull hex).1
  have hUE := h.extraspecial_thompson_moved_le_fixed hG T hempty hM hmany hJ hfull hex
  have hgZ := centralizer_le hseed hg
  have hfail : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      normalizer (E.map (MulAut.conj g).toMonoidHom : Set G) := by
    intro hj
    exact hgne (mem_normalizer_iff_map_conj_eq.mpr
      (h.thompsonFixed_conjugate_eq_of_maxJ_normalizes hG T hM hJ g hgZ hj))
  have hUg : U.map (MulAut.conj g).toMonoidHom = U := by
    ext u
    constructor
    · rintro ⟨u,hu,rfl⟩
      change g*u*g⁻¹ ∈ U
      rw [←hg u hu,mul_inv_cancel_right]
      exact hu
    · intro hu
      refine ⟨u,hu,?_⟩
      change g*u*g⁻¹ = u
      rw [←hg u hu,mul_inv_cancel_right]
  let := h.elementary
  have hEC : E ≤ centralizer (U : Set G) := by
    intro e he u hu
    exact congrArg V.subtype (mul_comm' (⟨u,(hUE hu).1⟩ : V) ⟨e,he.1⟩)
  have hEgC : E.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hEC).trans
      (map_centralizer_le_centralizer_image U (MulAut.conj g).toMonoidHom)
    have hs : (MulAut.conj g).toMonoidHom '' (U : Set G) = (U : Set G) :=
      congrArg (fun H : Subgroup G => (H : Set G)) hUg
    rwa [hs] at hh
  refine ⟨g,hg,hfail,le_inf hUE ?_,sup_le hEC hEgC⟩
  exact hUg.symm.le.trans (map_mono hUE)

end CFSG.Quasithin.Chapter15.Section01
