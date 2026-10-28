module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.Reduction

/-!
# Center action when the source subgroup contains the center

The marked coordinates express every member of X as a product of a member of
L and a power of the diagonal element. If the diagonal centralized Z(L), X would
centralize Z(L). When Z(L) lies in YS, a central involution would then lie in
N_YS(X) and commute with both marked three-cycles. No nonidentity involution in
S3 x S3 does this. Hence the diagonal moves Z(L), and the field and diagonal
induce the full center action.

The extra inclusion Z(L) <= YS is explicit: it holds in the source's local
setup, but is not a field of the general NormalizerGeometry record. These
specializations do not prove the unrestricted marked-cover calculation.
Source: Aschbacher--Smith 15.3.38, printed p.1136, manuscript of 1 March 2004.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- The marked three-subgroup is generated inside the cover and the diagonal cyclic group. -/
theorem three_le_linear_sup_diagonal {d : Overgroup L} (n : NormalizerGeometry d) :
    ((n.X : Subgroup n.YS).map n.YS.subtype) ≤ L ⊔ zpowers n.diagonalElement := by
  rintro _ ⟨x, hx, rfl⟩
  let xN : normalizer (n.X : Set n.YS) := ⟨x, (n.X : Subgroup n.YS).le_normalizer hx⟩
  have hm : n.coordinates xN ∈ (zpowers rotation).prod (zpowers rotation) := by
    rw [← n.three_coordinates]
    exact mem_map_of_mem _ hx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm.2
  let y := n.coordinates.symm ((n.coordinates xN).1, 1)
  have hyL : n.inclusion y ∈ L := by
    have hym : ((n.coordinates xN).1, 1) ∈
        (((n.X : Subgroup n.YS) ⊓ L.comap n.YS.subtype).subgroupOf
          (normalizer (n.X : Set n.YS))).map n.coordinates.toMonoidHom := by
      rw [n.linear_coordinates]
      exact ⟨hm.1, one_mem _⟩
    obtain ⟨t, ht, he⟩ := hym
    have hty : t = y := n.coordinates.injective
      (he.trans (n.coordinates.apply_symm_apply _).symm)
    exact (hty ▸ ht).2
  have hxy : xN = y * n.coordinates.symm (1, rotation) ^ k := by
    apply n.coordinates.injective
    simp only [map_mul, map_zpow, MulEquiv.apply_symm_apply, Prod.pow_mk,
      Prod.mk_mul_mk, one_mul, mul_one, one_zpow, y]
    exact Prod.ext rfl hk.symm
  have hxI : (x : I) = n.inclusion y * n.diagonalElement ^ k := by
    change n.inclusion xN = _
    rw [hxy, map_mul, map_zpow]
    rfl
  change (x : I) ∈ L ⊔ zpowers n.diagonalElement
  rw [hxI]
  exact (L ⊔ zpowers n.diagonalElement).mul_mem
    ((show L ≤ L ⊔ zpowers n.diagonalElement from le_sup_left) hyL)
    ((show zpowers n.diagonalElement ≤ L ⊔ zpowers n.diagonalElement from le_sup_right)
      (zpow_mem (mem_zpowers _) _))

private theorem symmetricThree_pair_cubic_fixer :
    ∀ q : SymmetricThree × SymmetricThree, q ^ 2 = 1 →
      (rotation, 1) * q = q * (rotation, 1) →
      (1, rotation) * q = q * (1, rotation) → q = 1 := by
  decide +kernel

/-- Containment of the center in YS supplies the nontrivial diagonal action. -/
theorem diagonal_moves_center_of_center_le_YS (d : Overgroup L)
    (n : NormalizerGeometry d) (hZ : (center L).map L.subtype ≤ n.YS) :
    n.diagonalElement ∉ centralizer ((center L).map L.subtype : Set I) := by
  intro hd
  have hLc : L ≤ centralizer ((center L).map L.subtype : Set I) := by
    rintro l hl z ⟨t, ht, rfl⟩
    exact (congrArg Subtype.val ((mem_center_iff.mp ht) ⟨l, hl⟩)).symm
  have hXc : ((n.X : Subgroup n.YS).map n.YS.subtype) ≤
      centralizer ((center L).map L.subtype : Set I) :=
    (three_le_linear_sup_diagonal n).trans (sup_le hLc (zpowers_le.mpr hd))
  let := d.cover.center_isKleinFour
  have htriv (z : center L) : z = 1 := by
    have hz : ((z : L) : I) ∈ (center L).map L.subtype := mem_map_of_mem _ z.property
    let zY : n.YS := ⟨z, hZ hz⟩
    have hzC : zY ∈ centralizer (n.X : Set n.YS) := by
      intro x hx
      exact Subtype.ext ((hXc (mem_map_of_mem n.YS.subtype hx) z hz).symm)
    let zN : normalizer (n.X : Set n.YS) := ⟨zY, centralizer_le_normalizer _ hzC⟩
    have hs : n.coordinates zN ^ 2 = 1 := by
      rw [← map_pow, ← map_one n.coordinates]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : center L => ((t : L) : I))
        (show z ^ 2 = 1 by rw [pow_two, IsKleinFour.mul_self])
    have hc (q : SymmetricThree × SymmetricThree)
        (hq : q ∈ (zpowers rotation).prod (zpowers rotation)) :
        q * n.coordinates zN = n.coordinates zN * q := by
      have hm : q ∈
          ((n.X : Subgroup n.YS).subgroupOf (normalizer (n.X : Set n.YS))).map
            n.coordinates.toMonoidHom := by rwa [n.three_coordinates]
      obtain ⟨x, hx, rfl⟩ := hm
      change n.coordinates x * n.coordinates zN = n.coordinates zN * n.coordinates x
      rw [← map_mul, ← map_mul]
      apply congrArg n.coordinates
      exact Subtype.ext (hzC x hx)
    have he : n.coordinates zN = 1 := symmetricThree_pair_cubic_fixer _ hs
      (hc (rotation, 1) ⟨mem_zpowers _, one_mem _⟩)
      (hc (1, rotation) ⟨one_mem _, mem_zpowers _⟩)
    have hzN : zN = 1 := n.coordinates.injective (he.trans (map_one _).symm)
    exact Subtype.ext (Subtype.ext (congrArg (fun t => n.inclusion t) hzN))
  have he : (center L) = (⊥ : Subgroup L) := by
    apply bot_unique
    intro z hz
    exact congrArg Subtype.val (htriv ⟨z, hz⟩)
  have hh := d.cover.center_isKleinFour.card_four
  rw [he, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hh
  contradiction

/-- Full action in the source specialization, with its additional inclusion explicit. -/
theorem centralFourAction_surjective_of_center_le_YS (d : Overgroup L)
    (n : NormalizerGeometry d) (hZ : (center L).map L.subtype ≤ n.YS) :
    Function.Surjective (centralFourAction d n.graphFieldI) :=
  centralFourAction_surjective_of_diagonal_moves d n
    (diagonal_moves_center_of_center_le_YS d n hZ)

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
