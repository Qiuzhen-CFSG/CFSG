module
public import Theory.SpecificGroups.PSL3Four.CentralCover.SylowFixedInnerFrattini
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The rank obstruction for a Sylow-fixed inner involution

The inner involution first forces the pure binary covering center to be
elementary. The full inverse image of a root plane of order sixteen is then
elementary, with order sixteen times the covering center. Thus a component
of two-rank at most four has trivial center. This uses the marked Sylow
fixing action, rather than a rank assertion for arbitrary central covers.

Source: Aschbacher–Smith, the component inspection in 2.4.29, printed p.546,
using I.2.2(3), printed pp.409–410.
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Four
open PSL3.LinearThree PSL3Even.UnipotentGeometry

/-- A native elementary root plane of the full projective group. -/
theorem exists_elementary_sixteen :
    ∃ A : Subgroup PSL, IsElementaryAbelian 2 A ∧ Nat.card A = 16 := by
  refine ⟨(V₁ F).map (projective F), IsElementaryAbelian.map _, ?_⟩
  rw [card_map_of_injective (projective_injective F), card_V₁, card_F]
  norm_num

/-- The marked inner action rules out a nontrivial center at binary rank four. -/
theorem center_eq_bot_of_sylow_fixed_inner_involution
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* PSL) (hZ : IsPGroup 2 (center E))
    (S : Sylow 2 E) (α : MulAut E) (hα : orderOf α = 2)
    (hi : α ∈ (MulAut.conj : E →* MulAut E).range)
    (hfix : ∀ y ∈ S, α y = y) (hrank : primeRank 2 E ≤ 4) :
    center E = ⊥ := by
  have hphi := inner_fixed_sylow_center_frattini e hZ S α hα hi hfix
  obtain ⟨A, hA, hcard⟩ := exists_elementary_sixteen
  let := hA
  let q := ElementaryParabolic.centerProjection e
  let B := A.comap q
  let : IsElementaryAbelian 2 B :=
    ElementaryParabolic.centerProjection_elementary_comap e hZ hphi A
  have hsmall : Nat.card B ≤ 16 :=
    (primeRank_le_iff_elementary_card_le E).mp hrank B inferInstance
  have hker : q.ker ≤ B := by
    intro x hx
    change q x ∈ A
    rw [show q x = 1 from hx]
    exact A.one_mem
  have hsize := IsElementaryAbelian.card_inf_ker_mul_card_map B q
  rw [inf_eq_right.mpr hker,
    show B.map q = A from map_comap_eq_self_of_surjective
      (ElementaryParabolic.centerProjection_surjective e) A,
    ElementaryParabolic.centerProjection_ker, hcard] at hsize
  apply card_eq_one.mp
  have hpos : 0 < Nat.card (center E) := Nat.card_pos
  nlinarith

end Matrix.PSL3Four
