module
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.Order.Atoms

/-!
# Irreducible odd quotients under a maximal two-group supplement

Let X be two-perfect and normalized by a two-group T, with T covered by XT.
A T-invariant subgroup of an odd abelian quotient of X lifts to a subgroup Y
normalized by X and T. The intermediate join YT is either T or XT. In the
first case its odd quotient is trivial; in the second, two-perfectness forces
X into Y. Thus the quotient action is irreducible.

The source application constructs membership in Ξ for the original tensor
point residual O²(C_{L₀}(z)), using the maximal Sylow subgroup in its actual
binary-plane wreath quotient. No ambient normality of X is assumed.
Source: Aschbacher--Smith 1.3.1 and the opening of 8.3.7, pp.508,724.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G A : Type*} [Group G] [Group A] [IsMulCommutative A]

/-- A maximal two-group supplement acts irreducibly on every nontrivial odd
abelian quotient of the two-perfect normal factor. The quotient map retains
its literal conjugation action. -/
theorem quotient_irreducible_of_twoPerfect_cover
    (X T : Subgroup G) (hX : IsPPerfect 2 X) (hT : IsPGroup 2 T)
    (hTX : T ≤ normalizer (X : Set G)) (hcover : T ⋖ X ⊔ T)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hA : IsPGroup p A)
    (q : X →* A) (hq : Function.Surjective q) (ρ : T →* MulAut A)
    (he : ∀ (t : T) (x : X),
      q (X.normalizerMonoidHom ⟨t,hTX t.property⟩ x) = ρ t (q x))
    (U : Subgroup A) (hU : ∀ t : T, ∀ u ∈ U, ρ t u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let B := U.comap q
  let Y := B.map X.subtype
  have hYX : Y ≤ X := map_subtype_le _
  have hXY : X ≤ normalizer (Y : Set G) := by
    let : B.Normal := (normal_of_isMulCommutative U).comap q
    have hh := B.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hTY : T ≤ normalizer (Y : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hmem : X.normalizerMonoidHom ⟨t,hTX ht⟩ x ∈ B := by
      change q (X.normalizerMonoidHom ⟨t,hTX ht⟩ x) ∈ U
      rw [he ⟨t,ht⟩ x]
      exact hU _ _ hx
    exact mem_map_of_mem X.subtype hmem
  have hsplit : Y ⊔ T = T ∨ Y ⊔ T = X ⊔ T :=
    hcover.eq_or_eq le_sup_right (sup_le (hYX.trans le_sup_left) le_sup_right)
  rcases hsplit with hsmall | hbig
  · left
    have hYT : Y ≤ T := le_sup_left.trans_eq hsmall
    have hB2 : IsPGroup 2 B :=
      (hT.comap_of_injective X.subtype X.subtype_injective).to_le
        (map_le_iff_le_comap.mp hYT)
    have hU2 : IsPGroup 2 U := by
      rw [←map_comap_eq_self_of_surjective hq U]
      exact hB2.map q
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 p hp.symm U U hU2 (hA.to_subgroup U))
  · right
    let H := X ⊔ T
    have hYH : Y ≤ H := hYX.trans le_sup_left
    let : (Y.subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le hXY hTY)
    have hX' : IsPPerfect 2 (X.subgroupOf H) :=
      hX.of_surjective (subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).symm.toMonoidHom
        (subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).symm.surjective
    have hgen : Y.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [←subgroupOf_sup hYH (show T ≤ H from le_sup_right),hbig,subgroupOf_self]
    have hle := le_normal_of_isPPerfect_of_le_sup_pGroup
      (X.subgroupOf H) (Y.subgroupOf H) (T.subgroupOf H) hX'
      hT.comap_subtype (hgen.symm ▸ le_top)
    have hXY' : X ≤ Y := by
      intro x hx
      exact hle (show (⟨x,(show X ≤ H from le_sup_left) hx⟩ : H) ∈ X.subgroupOf H from hx)
    apply top_unique
    intro a _
    obtain ⟨x,rfl⟩ := hq a
    obtain ⟨y,hy,hyx⟩ := hXY' x.property
    have hh : y = x := Subtype.ext hyx
    exact hh ▸ hy
end Theory.GroupTheory
