module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Inputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Envelope
public import Mathlib.Order.Minimal

/-!
# The nilpotent normalizer argument in 13.8.12

A proper subgroup containing the kernel of a map to a nilpotent group is
properly contained in its relative normalizer. For F inside O₂,F(H), the
actual map to the ordinary Fitting subgroup of H/O₂(H) has kernel
F ∩ O₂(H). Thus this normalizer argument applies to F ∩ M when O₂(H) ≤ M.

The identity needed by the source argument is O²(F ∩ M) = X whenever
X = O²(O₂,F(H) ∩ M) ≤ F ≤ O₂,F(H). We do not assert F ∩ M = X.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.12,
printed p.950. These intrinsic helpers are kept in the owned extension
while the surrounding chapter interfaces are being assembled.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
open Subgroup Theory.GroupTheory

theorem lt_relative_normalizer_of_nilpotent_image {G N : Type*} [Group G] [Group N] [Group.IsNilpotent N]
    (R E : Subgroup G) (hER : E < R) (f : R →* N)
    (hk : f.ker ≤ E.subgroupOf R) : E < R ⊓ normalizer (E : Set G) := by
  let q := f.rangeRestrict
  let D := E.subgroupOf R
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hker : q.ker ≤ D := by simpa only [q, D, MonoidHom.ker_rangeRestrict] using hk
  have he : (D.map q).comap q = D := comap_map_eq_self hker
  have hp : D.map q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    have hD : D = ⊤ := by rw [← he, ht, comap_top]
    exact hER.ne (le_antisymm hER.le (subgroupOf_eq_top.mp hD))
  obtain ⟨y, hyn, hy⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (D.map q) hp)
  obtain ⟨x, rfl⟩ := hq y
  have hxn : x ∈ normalizer (D : Set R) := by
    have hmem : x ∈ (normalizer (D.map q : Set f.range)).comap q := hyn
    rw [comap_normalizer_eq_of_surjective _ hq, he] at hmem
    exact hmem
  have hxE : (x : G) ∉ E := fun hx => hy (mem_map_of_mem q hx)
  have hxnorm : (x : G) ∈ normalizer (E : Set G) := by
    rw [← subgroupOf_normalizer_eq hER.le] at hxn
    exact hxn
  exact lt_of_le_of_ne (le_inf hER.le E.le_normalizer)
    (fun heq => hxE (heq.symm ▸ (show (x : G) ∈ R ⊓ normalizer (E : Set G) from ⟨x.property, hxnorm⟩)))

theorem normalizer_le_normalizer_twoResidual {G : Type*} [Group G] (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer (twoResidual E : Set G) := by
  exact (normal_subgroupOf_iff_le_normalizer
    ((twoResidual_le E).trans E.le_normalizer)).mp
    (normal_embedded_pResidual_subgroupOf 2 E.le_normalizer inferInstance)

theorem exists_fittingMap {G : Type*} [Group G] (H F : Subgroup G) (hF : F ≤ twoFitting H) :
    ∃ f : F →* fittingSubgroup (Source.Hstar H),
      f.ker = (Source.QH H).subgroupOf F := by
  let hFH := hF.trans (twoFitting_le H)
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hFH)
  have hf (x : F) : f x ∈ fittingSubgroup (Source.Hstar H) := by
    have hx : (⟨x, hFH x.property⟩ : H) ∈ twoFittingIn H := by
      rw [← twoFitting_subgroupOf H]
      exact hF x.property
    exact hx
  refine ⟨f.codRestrict _ hf, ?_⟩
  ext x
  change (⟨f x, hf x⟩ : fittingSubgroup (Source.Hstar H)) = 1 ↔ _
  rw [Subtype.ext_iff]
  change f x = 1 ↔ (x : G) ∈ (pCore 2 H).map H.subtype
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨⟨x, hFH x.property⟩, (QuotientGroup.eq_one_iff _).mp hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    have he' : y = inclusion hFH x := Subtype.ext he
    exact (QuotientGroup.eq_one_iff _).mpr (he' ▸ hy)

theorem twoResidual_eq_self {G : Type*} [Group G] (X : Subgroup G) (hp : IsPPerfect 2 X) :
    twoResidual X = X := by
  unfold twoResidual
  rw [(pResidual_eq_top_iff 2 X).mpr hp, ← MonoidHom.range_eq_map, range_subtype]

theorem intersection_residual_eq {G : Type*} [Group G] [Finite G] (H M F : Subgroup G)
    (hXF : residualInM H M ≤ F) (hFR : F ≤ twoFitting H) :
    twoResidual (F ⊓ M) = residualInM H M := by
  apply le_antisymm (twoResidual_mono (inf_le_inf_right M hFR))
  have hX : IsPPerfect 2 (residualInM H M) := isPPerfect_embedded_pResidual 2 _
  have he : twoResidual (residualInM H M) = residualInM H M := by
    unfold twoResidual
    rw [(pResidual_eq_top_iff 2 _).mpr hX, ← MonoidHom.range_eq_map, range_subtype]
  change residualInM H M ≤ twoResidual (F ⊓ M)
  rw [← he]
  exact twoResidual_mono (le_inf hXF ((residualInM_le H M).trans inf_le_right))

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
end
