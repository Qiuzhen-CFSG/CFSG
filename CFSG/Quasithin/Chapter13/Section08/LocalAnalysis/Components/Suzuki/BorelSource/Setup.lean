module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Images
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ActionInterface


/-!
# Source inputs and the invariant Borel contract for 13.8.16

`Earlier` records the precise earlier facts consumed by this step: relative
C-component membership and the source quotient model, the local Sylow and
orbit-index conditions of 1.2, the identity L₁ = θ(H ∩ M) of 13.7.3(9),
the two-by-three structure of L₁, and universal solvable exclusion from
13.8.13. Quasisimplicity of K* is the allowed input of 13.8.15.

These facts imply two-perfectness of L₁, its normalization by T, and
solvability of L₁T. No invariant Borel or centralization is included in
`Earlier`. The separate `InvariantBorel` is a construction target, retaining
the source parameter and the entire Borel in one or two actual Suzuki factors.
It is not an extra earlier-source assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.16,
printed pp.952–953; 13.7.3(9), p.936; Notation 13.2.1, p.877.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
variable {G : Type*} [Group G] [Finite G]

structure Earlier (H K L₁ T G₁ M : Subgroup G) (m : ℕ) where
  parameter_pos : 0 < m
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  star_quasisimple : IsQuasisimple (Source.starImage H K)
  model : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m
  base_le : L₁ ⊔ T ≤ H
  overgroup_le : H ≤ G₁
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H).map H.subtype = T
  sylow_le_M : T ≤ M
  generated : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)
  component_index : (normalizer (K.subgroupOf H : Set H)).index ≤ 2
  theta_eq : L₁ = theta (H ⊓ M)
  three_quotient : IsPGroup 3 (L₁ ⧸ pCore 2 L₁)
  solvable_exclusion : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
    Group.IsSolvable J → J ≤ M

variable {H K L₁ T G₁ M : Subgroup G} {m : ℕ}

namespace Earlier
variable (d : Earlier H K L₁ T G₁ M m)
include d

omit [Finite G] in
theorem orbit_le : conjugateSpanBy K T ≤ H :=
  conjugateSpanBy_le d.component_le ((le_sup_right.trans d.base_le).trans H.le_normalizer)

omit [Finite G] in
theorem intersection_normalizes : H ⊓ M ≤ normalizer (L₁ : Set G) := by
  rw [d.theta_eq]
  exact (H ⊓ M).le_normalizer.trans (normalizer_le_normalizer_theta _)

omit [Finite G] in
theorem sylow_normalizes : T ≤ normalizer (L₁ : Set G) :=
  (le_inf (le_sup_right.trans d.base_le) d.sylow_le_M).trans d.intersection_normalizes

theorem twoPerfect : IsPPerfect 2 L₁ := by
  rw [d.theta_eq]
  exact ComponentIntersection.theta_isPPerfect _

theorem base_solvable : Group.IsSolvable (L₁ ⊔ T : Subgroup G) := by
  let : Group.IsNilpotent (L₁ ⧸ pCore 2 L₁) := d.three_quotient.isNilpotent
  let : Group.IsNilpotent (pCore 2 L₁) := pCore_isNilpotent
  let : Group.IsSolvable L₁ := Group.isSolvable_of_ker_le_range (pCore 2 L₁).subtype
    (QuotientGroup.mk' (pCore 2 L₁)) (by rw [range_subtype, QuotientGroup.ker_mk'])
  have ht : IsPGroup 2 T := d.sylow_eq ▸ d.sylow.isPGroup'.map H.subtype
  let : Group.IsNilpotent T := ht.isNilpotent
  let A := L₁.subgroupOf (L₁ ⊔ T)
  let B := T.subgroupOf (L₁ ⊔ T)
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L₁.le_normalizer d.sylow_normalizes)
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show L₁ ≤ L₁ ⊔ T from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show L₁ ≤ L₁ ⊔ T from le_sup_left)).injective
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show T ≤ L₁ ⊔ T from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show T ≤ L₁ ⊔ T from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  rw [← subgroupOf_sup (show L₁ ≤ L₁ ⊔ T from le_sup_left) (show T ≤ L₁ ⊔ T from le_sup_right)]
  exact subgroupOf_self _

end Earlier

structure InvariantBorel (H K L₁ T : Subgroup G) (m : ℕ) where
  borel : Subgroup (Source.Hstar H)
  le_orbit : borel ≤ Source.starImage H (conjugateSpanBy K T)
  contains_sylow : Source.starImage H T ⊓ Source.starImage H (conjugateSpanBy K T) ≤ borel
  orbit_normalized : L₁ ⊔ T ≤ normalizer (conjugateSpanBy K T : Set G)
  normalized : Source.starImage H (L₁ ⊔ T) ≤ normalizer (borel : Set (Source.Hstar H))
  factors : ℕ
  factors_one_or_two : factors = 1 ∨ factors = 2
  equiv : Source.starImage H (conjugateSpanBy K T) ≃* (Fin factors → SuzukiMatrixGroup m)
  borel_map : (borel.subgroupOf (Source.starImage H (conjugateSpanBy K T))).map equiv.toMonoidHom =
    pi Set.univ (fun _ => SuzukiBorelSubgroup m)

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
