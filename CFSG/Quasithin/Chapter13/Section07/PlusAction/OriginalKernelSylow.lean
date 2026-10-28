module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponents
public import Theory.GroupTheory.NormalSylowQuotientAction
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
public import Theory.GroupTheory.ConjugateSpanKernel.CubicSupplement

/-!
# Sylow subgroups in the original plus kernel

Put C=C_H(UH/U₀), P=L₁T and R=O₂(P). The ordinary point residual is
2-perfect with cubic quotient. A normal subgroup of P not containing L₁
is therefore a 2-group. Since L₁ is not contained in the plus kernel,
C∩P≤R. Consequently R is Sylow in KR for every H-normal K≤C.

The selected primitive component application obtains normality from cubic
divisibility. This establishes the Sylow step before any classification of
K or commutator bound [K,L₁]≤O₂(K).

Source: Aschbacher--Smith, 13.7.4(1), printed pp.937--938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original plus kernel meets the point parabolic in its two-core. -/
theorem source_kernel_inf_point_le_radical
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    kernel F ⊓ (F.L₁ ⊔ (T : Subgroup G)) ≤ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let C := (kernel F).subgroupOf H
  let X := F.L₁.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  have hXH : F.L₁ ≤ H := le_sup_left.trans h.local_le
  let eX : X ≃* F.L₁ := subgroupOfEquivOfLe hXH
  have hp : IsPPerfect 2 X :=
    (isPPerfect_embedded_pResidual 2 _).of_surjective eX.symm.toMonoidHom eX.symm.surjective
  have hc : Nat.card (X ⧸ pCore 2 X) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)).toEquiv]
    rw [source_local_residual_eq d h]
    exact Section03.Noncentrality.ordinary_point_residual_quotient_card d eL
  have hTX : (T : Subgroup G) ≤ normalizer (F.L₁ : Set G) := by
    rw [source_local_residual_eq d h]
    exact T_normalizes_one L T V₁ d.line_stable
  have hSX : S ≤ normalizer (X : Set H) := by
    apply le_normalizer_iff.mpr
    intro s hs x hx
    exact (le_normalizer_iff.mp hTX) (s : G) hs (x : G) hx
  have hn : ¬ X ≤ C := by
    intro hh
    apply local_residual_not_le_kernel d h hne
    intro x hx
    exact hh (show (⟨x,hXH hx⟩ : H) ∈ X from hx)
  let : C.Normal := kernel_normal
  have htwo := twoGroup_kernel_on_cubic_residual_join X S C hp hc T.isPGroup'.comap_subtype hSX hn
  have hXS : X ⊔ S = P.subgroupOf H :=
    (subgroupOf_sup hXH h.T_le_H).symm
  have hCXS : IsPGroup 2 (C.subgroupOf (P.subgroupOf H)) := hXS ▸ htwo
  let f : C.subgroupOf (P.subgroupOf H) →* (kernel F ⊓ P : Subgroup G) :=
    (H.subtype.comp ((P.subgroupOf H).subtype.comp
      (C.subgroupOf (P.subgroupOf H)).subtype)).codRestrict _ (by
        intro x
        exact ⟨x.property,x.val.property⟩)
  have hf : Function.Surjective f := by
    intro x
    exact ⟨⟨⟨⟨x,h.local_le x.property.2⟩,x.property.2⟩,x.property.1⟩,rfl⟩
  have hpCP : IsPGroup 2 (kernel F ⊓ P : Subgroup G) := hCXS.of_surjective f hf
  apply le_pCoreIn_of_normalizes hpCP inf_le_right
  exact (le_inf (h.local_le.trans kernel_normalized) P.le_normalizer).trans
    inf_normalizer_le_normalizer_inf

/-- The point radical is Sylow in a normal kernel actor joined to that radical. -/
theorem source_normal_kernel_sylow
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  have hNR : (T : Subgroup G) ⊓ K ≤ R :=
    (le_inf (inf_le_right.trans hKC) (inf_le_left.trans le_sup_right)).trans
      (source_kernel_inf_point_le_radical d h eL hne)
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K
    (h.T_le_H.trans hKn)
  have hSR : (S : Subgroup K).map K.subtype ≤ R := by
    rw [hS,subgroupOf_map_subtype,inf_comm]
    simpa only [inf_comm] using hNR
  exact IsPGroup.exists_sylow_sup_of_coprime_index K R (isPGroup_pCoreIn 2 P)
    (((pCoreIn_le 2 P).trans h.local_le).trans hKn)
    (S : Subgroup K) S.not_dvd_index hSR

/-- The literal selected component inherits the Sylow conclusion from cubic
order divisibility, without assuming its small-model classification. -/
theorem source_primitive_kernel_sylow_of_three_dvd
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hKC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hd : 3 ∣ Nat.card (J ⧸ pCore 2 J)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    Chapter1.IsSylowIn 2 R (J.map H.subtype ⊔ R) :=
  source_normal_kernel_sylow d h eL hne hKC
    (source_primitive_kernel_normalizes_of_three_dvd d h hne J hJ hs hKC hd)

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
