module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Interface
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# Subnormal two-perfect groups and their maximal signalizers

A permutable two-subgroup supplement identifies X with the two-residual
of its join, so X is normal there. Mutual normalization then puts the
signalizer commutator in O₂(X). Every signalizer lies in C_M(X/O₂(X));
enlarging it to a Sylow subgroup of this centralizer proves that maximal
signalizers are exactly its Sylow two-subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.2(2)–(4), printed p. 57. The residual O² and the core O₂ are distinct.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G]

theorem residual_sup_of_permutable (X M R : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hRM : R ≤ M) (hR : IsPGroup 2 R)
    (hperm : (X : Set G) * (R : Set G) = (R : Set G) * (X : Set G)) :
    (pResidual 2 ↥(X ⊔ R)).map (X ⊔ R).subtype = X := by
  have hs : (X.subgroupOf (X ⊔ R)).IsSubnormal :=
    hsub.comap (inclusion (sup_le hXM hRM))
  have hx : IsPPerfect 2 (X.subgroupOf (X ⊔ R)) :=
    hX.of_surjective (subgroupOfEquivOfLe (show X ≤ X ⊔ R from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show X ≤ X ⊔ R from le_sup_left)).symm.surjective
  have he := pResidual_eq_of_subnormal_product
    (X.subgroupOf (X ⊔ R)) (R.subgroupOf (X ⊔ R)) hs hx hR.comap_subtype ?_
  · rw [he, map_subgroupOf_eq_of_le le_sup_left]
  · intro g
    have hg : (g : G) ∈ (X : Set G) * (R : Set G) := by
      rw [← coe_sup_of_set_mul_comm X R hperm]
      exact g.property
    obtain ⟨x, hx, r, hr, he⟩ := hg
    exact ⟨⟨x, mem_sup_left hx⟩, hx, ⟨r, mem_sup_right hr⟩, hr, Subtype.ext he⟩

theorem normal_sup_of_permutable (X M R : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hRM : R ≤ M) (hR : IsPGroup 2 R)
    (hperm : (X : Set G) * (R : Set G) = (R : Set G) * (X : Set G)) :
    (X.subgroupOf (X ⊔ R)).Normal := by
  have he := residual_sup_of_permutable X M R hXM hsub hX hRM hR hperm
  have he' : pResidual 2 ↥(X ⊔ R) = X.subgroupOf (X ⊔ R) := by
    apply (map_injective (X ⊔ R).subtype_injective)
    rw [he, map_subgroupOf_eq_of_le le_sup_left]
  rw [← he']
  infer_instance

theorem signalizer_le_normalizer (X M R : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hR : IsTwoSignalizer X M R) :
    R ≤ normalizer (X : Set G) := by
  have hn := normal_sup_of_permutable X M R hXM hsub hX hR.le hR.isPGroup
    (set_mul_normalizer_comm (X : Set G) R hR.normalizes)
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show X ≤ X ⊔ R from le_sup_left)).mp hn)

theorem signalizer_commutator_le_pCore (X M R : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hR : IsTwoSignalizer X M R) :
    ⁅X, R⁆ ≤ (pCore 2 X).map X.subtype :=
  commutator_le_pCore_of_mutual_normalization X R hR.isPGroup hR.normalizes
    (signalizer_le_normalizer X M R hXM hsub hX hR)
theorem signalizer_le_twoSectionCentralizer (X M R : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hR : IsTwoSignalizer X M R) :
    R ≤ twoSectionCentralizer X M :=
  (le_twoSectionCentralizer_iff X M R).mpr ⟨hR.le,
    signalizer_le_normalizer X M R hXM hsub hX hR,
    signalizer_commutator_le_pCore X M R hXM hsub hX hR⟩

theorem maximal_signalizer_iff_sylow (X M R : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) :
    IsMaximalTwoSignalizer X M R ↔
      ∃ S : Sylow 2 (twoSectionCentralizer X M),
        (S : Subgroup (twoSectionCentralizer X M)).map
          (twoSectionCentralizer X M).subtype = R := by
  rw [isMaximalTwoSignalizer_iff]
  constructor
  · intro hmax
    have hRC := signalizer_le_twoSectionCentralizer X M R hXM hsub hX hmax.1
    obtain ⟨S, hRS⟩ := (hmax.1.isPGroup.comap_subtype :
      IsPGroup 2 (R.subgroupOf (twoSectionCentralizer X M))).exists_le_sylow
    have hRS' : R ≤ (S : Subgroup (twoSectionCentralizer X M)).map
        (twoSectionCentralizer X M).subtype := by
      intro r hr
      exact ⟨⟨r, hRC hr⟩, hRS hr, rfl⟩
    exact ⟨S, le_antisymm (hmax.2 _ (sylow_twoSectionCentralizer_isSignalizer X M hXM S) hRS') hRS'⟩
  · rintro ⟨S, rfl⟩
    refine ⟨sylow_twoSectionCentralizer_isSignalizer X M hXM S, ?_⟩
    intro U hU hSU
    have hUC := signalizer_le_twoSectionCentralizer X M U hXM hsub hX hU
    have hSU' : (S : Subgroup (twoSectionCentralizer X M)) ≤
        U.subgroupOf (twoSectionCentralizer X M) := by
      intro s hs
      exact hSU (mem_map_of_mem _ hs)
    have he := S.is_maximal' hU.isPGroup.comap_subtype hSU'
    intro u hu
    exact ⟨⟨u, hUC hu⟩, he ▸ hu, rfl⟩
end CFSG.Quasithin.ChapterA.Section04

end
