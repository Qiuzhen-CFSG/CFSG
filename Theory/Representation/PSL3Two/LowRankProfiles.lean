module
public import Theory.Representation.PSL3Two.RankTwoOuterMovement
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces
public import Theory.Representation.BinaryNaturalDual.LowRankProfiles
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# Innerness of the marked low-rank natural--dual actors

An outer operator exchanges the two summands, so its displacement has dimension
at least three. The source budget excludes it in rank one. A quadratic actor
of larger order contains an inner involution; every actor fixes that
involution's displacement, whereas the existing root-movement calculation
shows that an outer operator moves a pure vector there. Thus the actor is
inner. The checked four-group geometry gives its rank bound and fixed space.

The final consumer retains a literal conjugation section and derives
quadraticity from its triple commutator. It supplies innerness rather than
assuming that a quotient automorphism preserves the two natural supports.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041, using the natural--dual
module of 14.6.22 and the F.9 quadratic fixed-codimension bound.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual.LowRankProfiles
variable (τ : Representation (ZMod 2) (MulAut Group) Space)
    (hinner : ∀ g : Group, τ (MulAut.conj g) = action g)

private noncomputable def operator (α : MulAut Group) : Space ≃ₗ[ZMod 2] Space :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom α)

include hinner

private theorem covariance (α : MulAut Group) (g : Group) (v : Space) :
    operator τ α (action g v) = action (α g) (operator τ α v) := by
  change τ α (action g v) = action (α g) (τ α v)
  rw [← hinner g, ← hinner (α g)]
  have he : α * MulAut.conj g = MulAut.conj (α g) * α := by
    ext k
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]

/-- Every outer implementation moves at least three dimensions. -/
theorem outer_displacement_bound (α : MulAut Group)
    (hα : α ∉ MulAut.innerSubgroup Group) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (τ α - LinearMap.id)) := by
  have hf := (outer_swaps α (operator τ α) (covariance τ hinner α) hα).1
  let j : Vector →ₗ[ZMod 2] LinearMap.range (τ α - LinearMap.id) :=
    ((τ α - LinearMap.id).comp (LinearMap.inl (ZMod 2) Vector
      (Module.Dual (ZMod 2) Vector))).codRestrict _ (fun v => ⟨(v,0),rfl⟩)
  have hj : Function.Injective j := by
    intro v w he
    have h := congrArg (fun x : LinearMap.range (τ α - LinearMap.id) => x.val.1) he
    change (τ α (v,0)).1 - v = (τ α (w,0)).1 - w at h
    change ∀ v : Vector, (τ α (v,0)).1 = 0 at hf
    rw [hf v,hf w,zero_sub,zero_sub] at h
    exact neg_injective h
  have hd := LinearMap.finrank_le_finrank_of_injective (f := j) hj
  simpa [Vector,Matrix.PSL3Two.Fano.Vector] using hd

/-- A quadratic four-group cannot contain an outer actor, since that actor
would move a pure vector in an inner involution's displacement. -/
theorem inner_of_quadratic_of_card_gt_two (A : Subgroup (MulAut Group))
    (hA : IsElementaryAbelian 2 A) (hc : 2 < Nat.card A)
    (hq : IsQuadratic τ A) : A ≤ MulAut.innerSubgroup Group := by
  let := hA
  let I := MulAut.innerSubgroup Group
  have hne : A ⊓ I ≠ ⊥ := by
    intro he
    let q : A →* MulAut.Outer Group := (QuotientGroup.mk' I).comp A.subtype
    have hi : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff q).mp
      apply bot_unique
      intro a ha
      have hai : (a : MulAut Group) ∈ I := (QuotientGroup.eq_one_iff _).mp ha
      have ha1 : (a : MulAut Group) = 1 := by
        have hm : (a : MulAut Group) ∈ A ⊓ I := ⟨a.property,hai⟩
        rwa [he,mem_bot] at hm
      exact Subtype.ext ha1
    have hcard := Nat.card_le_card_of_injective q hi
    rw [Matrix.PSL3Two.Automorphisms.card_outer_sl] at hcard
    omega
  obtain ⟨a,ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨g,hg⟩ := a.property.2
  have hi : Function.Injective (MulAut.conj : Group →* MulAut Group) :=
    MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hgA : MulAut.conj g ∈ A := hg.symm ▸ a.property.1
  have hg1 : g ≠ 1 := by
    intro he
    apply ha1
    apply Subtype.ext
    simp only [← hg,he,map_one,Subgroup.coe_one]
  have hg2 : g ^ 2 = 1 := by
    apply hi
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hgA
  intro α hα
  by_contra hout
  obtain ⟨v,⟨w,rfl⟩,hm⟩ := outer_moves_involution_displacement g hg2 hg1 α
    (operator τ α) (covariance τ hinner α) hout
  apply hm
  change τ α (action g w - w) = action g w - w
  rw [← hinner g]
  exact hq α hα (MulAut.conj g) hgA w

/-- The source's fixed-codimension budget also excludes the rank-one outer
case. Thus the complete nontrivial quadratic rank-one/rank-two actor is inner. -/
theorem inner_of_quadratic_budget (A : Subgroup (MulAut Group))
    (hA : IsElementaryTwo A) (hq : IsQuadratic τ A)
    (hbudget : fixedCodim τ A ≤ 2 * rank A) : A ≤ MulAut.innerSubgroup Group := by
  by_cases hc : 2 < Nat.card A
  · exact inner_of_quadratic_of_card_gt_two τ hinner A hA.2 hc hq
  have hcard : Nat.card A = 2 := by
    have hpos : 1 < Nat.card A := A.one_lt_card_iff_ne_bot.mpr hA.1
    omega
  have hr : rank A = 1 := by norm_num [rank,hcard]
  intro α hα
  by_contra hout
  have hlow := outer_displacement_bound τ hinner α hout
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hlow
  have hf : fixedSpace τ A ≤ fixedSpace τ (zpowers α) := by
    intro v hv a
    exact hv ⟨a,(zpowers_le.mpr hα) a.property⟩
  have hd := Submodule.finrank_mono hf
  have hsum := fixedCodim_add_finrank τ A
  have hsum' := fixedCodim_add_finrank τ (zpowers α)
  rw [hr] at hbudget
  omega
end BinaryLinearThree.NaturalDual.LowRankProfiles

namespace BinaryLinearThree.NaturalDual.LowRankProfiles
variable (τ : Representation (ZMod 2) (MulAut Group) Space)
    (hinner : ∀ g : Group, τ (MulAut.conj g) = action g)

include hinner

theorem fixedSpace_eq_naturalDualFixed (A : Subgroup (MulAut Group))
    (hAI : A ≤ MulAut.innerSubgroup Group) :
    fixedSpace τ A = FourGroupGeometry.naturalDualFixed A := by
  ext v
  rw [FourGroupGeometry.mem_naturalDualFixed]
  constructor
  · intro hv g hg
    change action g v = v
    rw [← hinner g]
    exact hv ⟨MulAut.conj g,hg⟩
  · intro hv a
    obtain ⟨g,hg⟩ := hAI a.property
    change τ (a : MulAut Group) v = v
    rw [← hg,hinner]
    exact hv g (hg.symm ▸ a.property)

/-- The four-group fixes exactly a three-space, with the literal contragredient
marking. Innerness is a conclusion of the source quadratic budget. -/
theorem rank_two_fixed_card (A : Subgroup (MulAut Group))
    (hA : IsElementaryTwo A) (hq : IsQuadratic τ A)
    (hbudget : fixedCodim τ A ≤ 2 * rank A) (hr : rank A = 2) :
    Nat.card (fixedSpace τ A) = 8 := by
  have hi := inner_of_quadratic_budget τ hinner A hA hq hbudget
  rw [fixedSpace_eq_naturalDualFixed τ hinner A hi]
  apply (FourGroupGeometry.FixedSpaces.naturalDualFixed_geometry A hi hA.2 _).1
  simpa [hr] using hA.card_eq_two_pow_rank
end BinaryLinearThree.NaturalDual.LowRankProfiles


namespace BinaryLinearThree.NaturalDual.LowRankProfiles

/-- The full automorphism bound leaves exactly the two source ranks. -/
theorem rank_one_or_two (A : Subgroup (MulAut Group)) (hA : IsElementaryTwo A) :
    rank A = 1 ∨ rank A = 2 := by
  have hc := FourGroupGeometry.elementary_card_le_four A hA.2
  have hp := hA.card_eq_two_pow_rank
  have hpos := hA.rank_pos
  have hr : rank A ≤ 2 := by
    by_contra hn
    have hpow : 2 ^ 3 ≤ 2 ^ rank A := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega

/-- On the actual quotient coordinates the source commutator and numerical
bound force innerness and rank one or two, without any fusion hypothesis. -/
theorem section_inner_and_rank
    {J : Type*} [_root_.Group J] (H B Z A : Subgroup J)
    (τ : Representation (ZMod 2) (MulAut Group) Space)
    (hinner : ∀ g : Group, τ (MulAut.conj g) = action g)
    (π : H →* MulAut Group)
    (c : BinaryConjugationSection H B Z (τ.comp π))
    (hA : IsElementaryTwo ((A.subgroupOf H).map π))
    (hc : ⁅A,⁅A,B⁆⁆ ≤ Z)
    (hbudget : fixedCodim τ ((A.subgroupOf H).map π) ≤
      2 * rank ((A.subgroupOf H).map π)) :
    ((A.subgroupOf H).map π) ≤ MulAut.innerSubgroup Group ∧
      (rank ((A.subgroupOf H).map π) = 1 ∨ rank ((A.subgroupOf H).map π) = 2) := by
  exact ⟨inner_of_quadratic_budget τ hinner _ hA
    (BinaryConjugationSection.isQuadratic_of_triple_commutator_le H B Z A τ π c hc) hbudget,
    rank_one_or_two _ hA⟩

end BinaryLinearThree.NaturalDual.LowRankProfiles
