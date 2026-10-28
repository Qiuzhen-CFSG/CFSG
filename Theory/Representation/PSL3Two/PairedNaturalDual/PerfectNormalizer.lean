module
public import Theory.Representation.PSL3Two.PairedNaturalDual
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.Commutator.NormalizedPerfectSmallIndex
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# Perfect normalizers in a marked pair of binary linear-three components

Perfectness fixes each member of a permuted pair of supports. A perfect
subgroup of Aut(SL₃(2)) is either trivial or the full inner group: its outer
image is solvable, and every proper subgroup of SL₃(2) is solvable.

A perfect group normalizing a nontrivial group of order at most four fixes
it pointwise. If its projections on both components were nontrivial, both
would be full inner groups, whose automorphism centralizers are trivial.
Joint faithfulness would then kill the small actor. Consequently one
projection is trivial; the actual component embeddings place the perfect
group in the other factor.

This supplies the diagonal exclusion in Aschbacher--Smith 14.6.24(3),
printed p.1040. The Chapter14 consumer supplies the same original quotient
actor and opposite component, rather than an independent diagonal subgroup.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace BinaryLinearThree.NaturalDual.Paired
variable {H E : Type*} [_root_.Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- A perfect subgroup fixes each member of a permuted pair of subspaces. -/
theorem perfect_le_pair_stabilizer [Finite H]
    (ρ : Representation (ZMod 2) H E) (I J : Submodule (ZMod 2) E)
    (hperm : ∀ a : H, (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I))
    (B : Subgroup H) [_root_.Group.IsPerfect B] :
    B ≤ subspaceStabilizer ρ I ⊓ subspaceStabilizer ρ J := by
  let N := subspaceStabilizer ρ I ⊓ subspaceStabilizer ρ J
  have hmem (a : H) : a ∈ N ↔ I.map (ρ a) = I ∧ J.map (ρ a) = J :=
    and_congr (subspace_map_eq_iff ρ I a).symm (subspace_map_eq_iff ρ J a).symm
  by_cases hN : N = ⊤
  · change B ≤ N
    rw [hN]
    exact le_top
  obtain ⟨a,ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN)
  have hswap := (hperm a).resolve_left (fun h => ha.2 ((hmem a).mpr h))
  have hi : N.index ∣ 2 := (index_dvd_two_iff').mpr ⟨a,fun b => by
    rcases hperm b with hb | hb
    · exact Or.inr ((hmem b).mpr hb)
    · apply Or.inl
      apply (hmem (a*b)).mpr
      constructor <;> rw [map_mul]
      · change I.map ((ρ a).comp (ρ b)) = I
        rw [Submodule.map_comp,hb.1,hswap.2]
      · change J.map ((ρ a).comp (ρ b)) = J
        rw [Submodule.map_comp,hb.2,hswap.1]⟩
  exact le_of_isPerfect_of_index_le_four B N ((Nat.le_of_dvd (by decide) hi).trans (by decide))

/-- Perfect subgroups of Aut(SL₃(2)) are trivial or the full inner group. -/
theorem perfect_aut_eq_bot_or_inner (B : Subgroup (MulAut Group))
    [_root_.Group.IsPerfect B] : B = ⊥ ∨ B = MulAut.innerSubgroup Group := by
  let : _root_.Group.IsNilpotent (MulAut.Outer Group) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.isNilpotent
  obtain ⟨f,hf,he⟩ := MulAut.perfect_subgroup_exists_inner_lift B Matrix.PSL3Two.center_eq_bot
  let : _root_.Group.IsPerfect f.range := _root_.Group.IsPerfect.range f
  by_cases ht : f.range = ⊤
  · right
    apply le_antisymm (MulAut.perfect_subgroup_le_inner B)
    rintro _ ⟨g,rfl⟩
    obtain ⟨b,hb⟩ := (MonoidHom.range_eq_top.mp ht) g
    rw [←hb,he]
    exact b.property
  · left
    let : _root_.Group.IsSolvable f.range := Matrix.PSL3Two.isSolvable_subgroup_SL_of_ne_top _ ht
    have hz : Subsingleton f.range := by
      by_contra! hn
      exact _root_.Group.IsPerfect.not_isSolvable f.range inferInstance
    apply bot_unique
    intro b hb
    apply Subgroup.mem_bot.mpr
    have hh : f ⟨b,hb⟩ = 1 := congrArg Subtype.val (hz.elim (f.rangeRestrict ⟨b,hb⟩) 1)
    exact (he ⟨b,hb⟩).symm.trans (by rw [hh,map_one])

namespace Marking
variable [Finite H] {ρ : Representation (ZMod 2) H E} (m : Marking ρ)

/-- A perfect normalizer of a nontrivial actor of order at most four cannot
project onto both component inner groups. This excludes the diagonal case. -/
theorem perfect_normalizer_projection_trivial (hf : Function.Injective ρ)
    (A B : Subgroup H) (hA : A ≠ ⊥) (hc : Nat.card A ≤ 4)
    [_root_.Group.IsPerfect B] (hn : B ≤ normalizer (A : Set H)) :
    B.map m.left = ⊥ ∨ B.map m.right = ⊥ := by
  have hcomm : ⁅A,B⁆ = ⊥ := le_bot_iff.mp
    (commutator_le_of_perfect_normalized_small_index B A ⊥ hn
      (by intro b _; apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr; exact Subgroup.map_bot _) (by simpa using hc))
  let : _root_.Group.IsPerfect (B.map m.left) := _root_.Group.IsPerfect.map m.left
  let : _root_.Group.IsPerfect (B.map m.right) := _root_.Group.IsPerfect.map m.right
  rcases perfect_aut_eq_bot_or_inner (B.map m.left) with hl | hl
  · exact Or.inl hl
  rcases perfect_aut_eq_bot_or_inner (B.map m.right) with hr | hr
  · exact Or.inr hr
  exfalso
  apply hA
  apply bot_unique
  intro a ha
  apply Subgroup.mem_bot.mpr
  apply (injective_iff_map_eq_one _).mp (m.joint_injective hf)
  have htriv (f : H →* MulAut Group) (hB : B.map f = MulAut.innerSubgroup Group) : f a = 1 := by
    have hh : f a ∈ centralizer (MulAut.innerSubgroup Group : Set (MulAut Group)) := by
      rw [←hB]
      rintro _ ⟨b,hb,rfl⟩
      simpa only [map_mul] using congrArg f
        ((commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb)
    rwa [MulAut.centralizer_innerSubgroup_eq_bot Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
  exact Prod.ext (htriv m.left hl) (htriv m.right hr)

/-- With the literal factor embeddings, the perfect normalizer lies in
one original factor. Neither a diagonal identification nor an abstract
isomorphism of the perfect subgroup is required. -/
theorem perfect_normalizer_le_factor (hf : Function.Injective ρ)
    (A B : Subgroup H) (hA : A ≠ ⊥) (hc : Nat.card A ≤ 4)
    [_root_.Group.IsPerfect B] (hn : B ≤ normalizer (A : Set H))
    (κ₁ κ₂ : Group →* H)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k) :
    B ≤ κ₁.range ∨ B ≤ κ₂.range := by
  let : _root_.Group.IsNilpotent (MulAut.Outer Group) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.isNilpotent
  let : _root_.Group.IsPerfect (B.map m.left) := _root_.Group.IsPerfect.map m.left
  let : _root_.Group.IsPerfect (B.map m.right) := _root_.Group.IsPerfect.map m.right
  have hl := MulAut.perfect_subgroup_le_inner (B.map m.left)
  have hr := MulAut.perfect_subgroup_le_inner (B.map m.right)
  rcases m.perfect_normalizer_projection_trivial hf A B hA hc hn with hz | hz
  · right
    intro b hb
    obtain ⟨k,hk⟩ := hr (mem_map_of_mem m.right hb)
    refine ⟨k,?_⟩
    apply m.joint_injective hf
    have hb0 : m.left b = 1 := by
      have := mem_map_of_mem m.left hb
      rwa [hz,mem_bot] at this
    exact Prod.ext ((hl₂ k).trans hb0.symm) ((hr₂ k).trans hk)
  · left
    intro b hb
    obtain ⟨k,hk⟩ := hl (mem_map_of_mem m.left hb)
    refine ⟨k,?_⟩
    apply m.joint_injective hf
    have hb0 : m.right b = 1 := by
      have := mem_map_of_mem m.right hb
      rwa [hz,mem_bot] at this
    exact Prod.ext ((hl₁ k).trans hk) ((hr₁ k).trans hb0.symm)
end Marking
end BinaryLinearThree.NaturalDual.Paired
