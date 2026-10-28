module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.Movement
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleKernel
public import Theory.GroupTheory.CharacteristicCoreCenter

/-!
# Exact C.2.7 kernel and reducedness

The normal component source in C.2.7 uses the literal omega-center of O₂(KR).
Characteristic-normalizer control forces nontrivial action; quasisimple kernel
structure and maximum elementary subgroups give the actual source clauses.

Source: Aschbacher--Smith, C.2.7(1–2), printed pp.145–146.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

theorem kernel_of_normal_component (K R M : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPRadical 2 R)
    (hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ K ≤ M) :
    KernelConclusion K R := by
  let J := K ⊔ R
  let K₀ := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hgen : K₀ ⊔ R₀ = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hKC : ¬ K₀ ≤ starKernel K R := outside_moves_starV K R M hr hc hcontrol hout
  have h := QuasisimpleKernel.normal_kernel_structure K₀ R₀ (starKernel K R)
    (hK.subgroupOf (show K ≤ J from le_sup_left)) hr.isPGroup.comap_subtype hgen
    (core_le_starKernel K R) hKC
  have heC : coreCenterImage K R = K₀.coreCenterIn 2 := by
    apply map_injective J.subtype_injective
    rw [map_coreCenterIn_of_injective 2 K₀ J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)]
    rw [coreCenterImage,map_map,coreCenterIn,Subgroup.upperCentralSeriesStep_eq_comap_center]
    rfl
  refine ⟨core_le_starKernel K R,?_,⟨inferInstance,inferInstance,h.2⟩⟩
  change starKernel K R ≤ pCore 2 J ⊔ coreCenterImage K R
  rw [heC,coreCenterIn,Subgroup.upperCentralSeriesStep_eq_comap_center]
  exact h.1
end CFSG.Quasithin.ChapterC.C27Source
