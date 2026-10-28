module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The solvable envelope used in 13.8.14

The ordinary Fitting subgroup of H/O₂(H) is nilpotent. Its inverse image
is solvable, since its kernel is a two-group. This inverse image is normal
in H, so adjoining any solvable subgroup of H again gives a solvable group.
Consequently the solvable-overgroup exclusion, once proved, applies to
O₂,F(H)L₁T and identifies the two residuals appearing in 13.8.12 and 13.8.14.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.14,
printed p.951. This module proves the extension step without assuming
the solvable-overgroup exclusion.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

theorem twoFittingIn_normal (H : Subgroup G) : (twoFittingIn H).Normal := by
  unfold twoFittingIn
  infer_instance

theorem twoFitting_subgroupOf (H : Subgroup G) :
    (twoFitting H).subgroupOf H = twoFittingIn H := by
  exact comap_map_eq_self_of_injective H.subtype_injective _

theorem le_normalizer_twoFitting (H : Subgroup G) :
    H ≤ normalizer (twoFitting H : Set G) := by
  have hn : ((twoFitting H).subgroupOf H).Normal := by
    rw [twoFitting_subgroupOf]
    exact twoFittingIn_normal H
  exact (normal_subgroupOf_iff_le_normalizer (twoFitting_le H)).mp hn

theorem twoFittingIn_solvable [Finite G] (H : Subgroup G) :
    Group.IsSolvable (twoFittingIn H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    infer_instance
  let := hk
  exact isSolvable_comap_of_solvable_ker q _

theorem twoFitting_solvable [Finite G] (H : Subgroup G) :
    Group.IsSolvable (twoFitting H) := by
  let := twoFittingIn_solvable H
  exact Group.isSolvable_of_surjective
    (f := ((twoFittingIn H).equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
    ((twoFittingIn H).equivMapOfInjective H.subtype H.subtype_injective).surjective

theorem twoFitting_sup_solvable [Finite G] {H A : Subgroup G}
    (hA : A ≤ H) (hs : Group.IsSolvable A) :
    Group.IsSolvable ↥(twoFitting H ⊔ A) := by
  let F := twoFitting H
  let J := F ⊔ A
  have hn : J ≤ normalizer (F : Set G) :=
    (sup_le (twoFitting_le H) hA).trans (le_normalizer_twoFitting H)
  let : (F.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hn
  let := twoFitting_solvable H
  let := hs
  let : Group.IsSolvable (F.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show F ≤ J from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show F ≤ J from le_sup_left)).injective
  let : Group.IsSolvable (A.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show A ≤ J from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show A ≤ J from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (F.subgroupOf J) (A.subgroupOf J)
    (codisjoint_subgroupOf_sup F A).eq_top

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
