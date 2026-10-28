module
public import CFSG.Quasithin.Chapter10.SourceNonnormalFixedResidual
public import Theory.GroupTheory.CComponent.IntersectionCover

/-!
# The original covering intersection component

Let M = N_G(L₀) in the Fundamental Setup. If I ≤ M covers L₀ modulo
its two-core and I ≤ H, then the literal residual (L ∩ H)^∞ is a
C-component of H ∩ M and covers L modulo O₂(L). The argument works
inside M, where L is a C-component; it never requires L normal in M.

This supplies the intersection-component step in Aschbacher–Smith,
4.2.4 and its use in 4.2.12 (combined manuscript, 1 March 2004,
printed pp.608 and 610). The subsequent C.4.8 normality conclusion
remains a separate classification input.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- A covering subgroup in the original setup supplies the literal
intersection C-component and its two-core cover. -/
theorem source_covering_intersection_component
    {I H : Subgroup G} (hIM : I ≤ D.maximalLocal) (hIH : I ≤ H)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G)) :
    (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf
      (H ⊓ D.maximalLocal)).IsCComponent ∧
    (L : Set G) =
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype : Set G) *
        (L.pCoreIn 2 : Set G) := by
  let M := D.maximalLocal
  let X := localOrbit T L
  let U := H ⊓ M
  let C := L.subgroupOf M
  let P := U.subgroupOf M
  let Z := C ⊓ P
  let A := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := (solvableResidual Z).map Z.subtype
  have hLM : L ≤ M := (le_componentOrbit L T).trans X.le_normalizer
  have hUM : U ≤ M := inf_le_right
  have hLH : L ⊓ H ≤ M := inf_le_left.trans hLM
  have hAU : A ≤ U := le_inf ((map_subtype_le _).trans inf_le_right)
    ((map_subtype_le _).trans hLH)
  let : Group.IsNilpotent (pCore 2 M) := pCore_isPGroup.isNilpotent
  have hc : (C : Set M) ⊆ (P : Set M) * (pCore 2 M : Set M) := by
    intro l hl
    obtain ⟨i, hi, n, hn, he⟩ := hcover ((le_componentOrbit L T) hl)
    have hnM : n ∈ M.pCoreIn 2 :=
      (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl) hn
    obtain ⟨nM, hnM, rfl⟩ := hnM
    exact ⟨⟨i, hIM hi⟩, ⟨hIH hi, hIM hi⟩, nM, hnM, Subtype.ext he⟩
  obtain ⟨hRcomp, hcoverC⟩ := D.component_in_maximalLocal.intersection_residual_cover
    (pCore 2 M) hc
  have hZ : Z = (L ⊓ H).subgroupOf M := by
    ext m
    exact and_congr_right (fun _ => and_iff_left m.property)
  let e : Z ≃* (L ⊓ H : Subgroup G) :=
    (MulEquiv.subgroupCongr hZ).trans (subgroupOfEquivOfLe hLH)
  have he : (L ⊓ H).subtype.comp e.toMonoidHom = M.subtype.comp Z.subtype := rfl
  have hRA : R.map M.subtype = A := by
    change ((solvableResidual Z).map Z.subtype).map M.subtype = A
    rw [map_map, ← he, ← map_map, map_solvableResidual_eq e.toMonoidHom e.surjective]
  let eU := subgroupOfEquivOfLe hUM
  have hAcomp : (A.subgroupOf U).IsCComponent := by
    have h := hRcomp.map_equiv eU
    have hr : (R.subgroupOf P).map eU.toMonoidHom = A.subgroupOf U := by
      apply map_injective U.subtype_injective
      rw [map_subgroupOf_eq_of_le hAU, map_map]
      change (R.subgroupOf P).map (M.subtype.comp P.subtype) = A
      rw [← map_map, map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right)]
      exact hRA
    rwa [hr] at h
  refine ⟨hAcomp, ?_⟩
  apply Set.Subset.antisymm
  · intro l hl
    obtain ⟨r, hr, n, hn, he'⟩ := hcoverC.subset (show (⟨l,hLM hl⟩ : M) ∈ C from hl)
    have hnL : (n : G) ∈ L.pCoreIn 2 := by
      have heN : C ⊓ pCore 2 M = C.pCoreIn 2 := by
        apply le_antisymm
        · intro x hx
          change x ∈ (pCore 2 C).map C.subtype
          rw [pCore_subnormal_eq_comap 2 D.component_in_maximalLocal.subnormal]
          exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
        · exact le_inf (pCoreIn_le 2 C)
            (pCoreIn_le_of_subnormal 2 D.component_in_maximalLocal.subnormal)
      have hnC := heN ▸ hn
      have hnmap : (n : G) ∈ (C.pCoreIn 2).map M.subtype := ⟨n,hnC,rfl⟩
      rw [map_pCoreIn_of_injective 2 _ _ M.subtype_injective,
        map_subgroupOf_eq_of_le hLM] at hnmap
      exact hnmap
    refine ⟨r, ?_, n, hnL, congrArg Subtype.val he'⟩
    change (r : G) ∈ A
    rw [← hRA]
    exact ⟨r,hr,rfl⟩
  · rintro _ ⟨a,ha,n,hn,rfl⟩
    exact L.mul_mem (((map_subtype_le _).trans inf_le_left) ha) (pCoreIn_le 2 L hn)
end CFSG.Quasithin.Chapter10
