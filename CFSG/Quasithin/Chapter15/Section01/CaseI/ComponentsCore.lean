module
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.Fitting.OutsideComponent
/-!
# Core recovery and component extraction in Case I

A.4.4(1) recovers O₂(H)=O₂(M_Z) whenever M_Z≤H≤G₁ and the preimage
of F*(H/O₂(H)) lies in M_Z. The source normalizer bound then forces H=M_Z.
At H=G₁ this gives escape of that preimage, and the genuine quotient
component correspondence supplies an outside C-component with quasisimple
two-core quotient once O₂,F(G₁) has been placed in M_Z.

Source: Aschbacher--Smith 15.1.19(4),(6), printed p.1093, and A.4.4(1).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- The full quotient Fitting preimage recovers the core in an overgroup. -/
theorem caseI_overgroup_core_eq (H M : Subgroup G) (hMH : M ≤ H)
    (hf : twoGeneralizedFittingPreimage H ≤ M) : H.pCoreIn 2 = M.pCoreIn 2 := by
  have ha : IntersectionAlternative
      (twoCoreQuotientImage H (twoGeneralizedFittingPreimage H)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl, ?_, ?_⟩
    · exact (inferInstance :
        ((generalizedFitting (H ⧸ pCore 2 H)).subgroupOf
          (generalizedFitting (H ⧸ pCore 2 H))).Normal).isSubnormal
    · apply (closure_le _).mpr
      intro x hx
      exact hx.1.1
  have h := lemma_A_4_4_1 H M (twoGeneralizedFittingPreimage H)
    (twoCore_le_fittingPreimage H) (le_inf (map_subtype_le _) hf) ha
  simpa only [inf_eq_right.mpr hMH] using h

/-- Original 15.1.19(4), using the actual relative core normalizer from 15.1.18(5). -/
theorem caseI_overgroup_eq (G1 M H : Subgroup G)
    (hMH : M ≤ H) (hHG : H ≤ G1)
    (hn : G1 ⊓ normalizer (M.pCoreIn 2 : Set G) ≤ M)
    (hf : twoGeneralizedFittingPreimage H ≤ M) : H = M := by
  apply le_antisymm _ hMH
  apply le_trans _ hn
  apply le_inf hHG
  rw [← caseI_overgroup_core_eq H M hMH hf]
  exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

/-- The intrinsic full preimage is forced outside every proper core-normalizer overgroup. -/
theorem caseI_fittingPreimage_not_le (M : Subgroup G)
    (hproper : M ≠ ⊤) (hn : normalizer (M.pCoreIn 2 : Set G) ≤ M) :
    ¬ (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M := by
  intro hf
  let Q := pCore 2 G
  have hcoreeq : M.pCoreIn 2 = Q := by
    let H := (⊤ : Subgroup G)
    let e : H ≃* G := topEquiv
    have hp : twoGeneralizedFittingPreimage H ≤ M := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      apply hf
      let eqv := QuotientGroup.congr (pCore 2 H) (pCore 2 G) e (pCore_map_iso 2 e)
      change QuotientGroup.mk' (pCore 2 H) y ∈ generalizedFitting (H ⧸ pCore 2 H) at hy
      have hh := mem_map_of_mem eqv.toMonoidHom hy
      rw [map_generalizedFitting_equiv] at hh
      exact hh
    have he := caseI_overgroup_core_eq H M le_top hp
    have ht : H.pCoreIn 2 = Q := pCore_map_iso 2 e
    exact he.symm.trans ht
  have htop : normalizer (M.pCoreIn 2 : Set G) = ⊤ := by
    rw [hcoreeq]
    exact normalizer_eq_top _
  exact hproper (top_unique (htop ▸ hn))

/-- Actual C-component extraction after the local Fitting containment. -/
theorem caseI_exists_component_of_twoFittingCore_le (M : Subgroup G)
    (hproper : M ≠ ⊤) (hn : normalizer (M.pCoreIn 2 : Set G) ≤ M)
    (hf : twoFittingCore G ≤ M) :
    ∃ L : Subgroup G, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧ ¬ L ≤ M :=
  exists_cComponent_outside_of_fitting_preimage_le M hf
    (caseI_fittingPreimage_not_le M hproper hn)
end CFSG.Quasithin.Chapter15.Section01
