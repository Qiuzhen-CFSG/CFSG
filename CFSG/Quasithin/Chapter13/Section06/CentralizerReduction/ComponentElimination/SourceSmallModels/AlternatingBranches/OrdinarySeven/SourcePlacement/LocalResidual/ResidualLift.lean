module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Residual recognition across a two-group action kernel

A normal two-perfect subgroup equals the two-residual if its image has
two-power index and the action kernel is a two-group. Functoriality puts
the residual in the subgroup times the kernel; two-perfectness then removes
the kernel. The ambient version retains each subgroup restriction and uses
only relative normality. Its consumer is the ordinary A₇ source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, ordinary A₇ paragraph, printed p.932 (PDF p.949).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

-- Residuals lift through two-kernels using relative normality alone.
theorem residual_eq_of_image_index (A : Subgroup G) [A.Normal]
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hA : IsPPerfect 2 A)
    (hi : ∃ n, (A.map q).index = 2 ^ n) : pResidual 2 G = A := by
  have : (A.map q).Normal := Subgroup.Normal.map inferInstance q hq
  obtain ⟨n, hn⟩ := hi
  have hp : IsPGroup 2 (Q ⧸ A.map q) := IsPGroup.of_card hn
  have hm : (pResidual 2 G).map q ≤ A.map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact sInf_le ⟨inferInstance, hp⟩
  apply le_antisymm ?_ (le_pResidual_of_isPPerfect A hA)
  apply le_normal_of_isPPerfect_of_le_sup_pGroup (pResidual 2 G) A q.ker
    (isPPerfect_pResidual 2) hk
  rw [← comap_map_eq]
  exact map_le_iff_le_comap.mp hm

-- All subgroups and kernels below are in their literal ambient groups.
theorem ambient_residual_eq_of_image_index
    (H A : Subgroup G) (hAH : A ≤ H) (hn : (A.subgroupOf H).Normal)
    (q : G →* Q) (hk : IsPGroup 2 q.ker) (hA : IsPPerfect 2 A)
    (hi : ∃ n, (A.map q).relIndex (H.map q) = 2 ^ n) :
    A = (pResidual 2 H).map H.subtype := by
  let f : H →* H.map q := q.subgroupMap H
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.comap H.subtype := by
      ext x
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  have he : (A.subgroupOf H).map f = (A.map q).subgroupOf (H.map q) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hAH hx⟩, hx, Subtype.ext hxy⟩
  let := hn
  have ha : IsPPerfect 2 (A.subgroupOf H) :=
    hA.of_surjective (subgroupOfEquivOfLe hAH).symm.toMonoidHom
      (subgroupOfEquivOfLe hAH).symm.surjective
  have hr : pResidual 2 H = A.subgroupOf H :=
    residual_eq_of_image_index (A.subgroupOf H) f hf hfker ha (by rwa [he])
  rw [hr, map_subgroupOf_eq_of_le hAH]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
theorem residual_eq_of_action_index
    (H A N : Subgroup G) (hAH : A ≤ H) (hNH : N ≤ H) (hAN : A ≤ N)
    (hn : (A.subgroupOf N).Normal) (q : H →* Q) (hk : IsPGroup 2 q.ker)
    (hA : IsPPerfect 2 A)
    (hi : ∃ n, ((A.subgroupOf H).map q).relIndex ((N.subgroupOf H).map q) = 2 ^ n) :
    A = (pResidual 2 N).map N.subtype := by
  have hAn : A.subgroupOf H ≤ N.subgroupOf H := subgroupOf_mono H hAN
  have hnorm : ((A.subgroupOf H).subgroupOf (N.subgroupOf H)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro x hx
    rw [← subgroupOf_normalizer_eq hAH]
    exact (normal_subgroupOf_iff_le_normalizer hAN).mp hn hx
  have ha : IsPPerfect 2 (A.subgroupOf H) :=
    hA.of_surjective (subgroupOfEquivOfLe hAH).symm.toMonoidHom
      (subgroupOfEquivOfLe hAH).symm.surjective
  have he := ambient_residual_eq_of_image_index (N.subgroupOf H) (A.subgroupOf H)
    hAn hnorm q hk ha hi
  have hm := congrArg (map H.subtype) he
  rw [map_subgroupOf_eq_of_le hAH, map_embedded_pResidual,
    map_subgroupOf_eq_of_le hNH] at hm
  exact hm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
end
