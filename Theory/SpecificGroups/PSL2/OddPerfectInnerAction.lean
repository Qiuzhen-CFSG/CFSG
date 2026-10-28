module
public import Theory.SpecificGroups.PSL2.BinaryPerfectCentralizer
public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup

public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Perfect inner subgroups of odd PSL₂ automorphism groups

Perfect subgroups of an odd-field PSL₂ have trivial two-core. The faithful
inner action transports that statement to subgroups of its automorphism group.
A nontrivial perfect subgroup has trivial centralizer in PSL₂, so its inner
image's full automorphism centralizer embeds in the outer quotient. In field
degrees one and two that quotient is a two-group.

These bounds control the actual secondary action in the proper two-local
inspection of Aschbacher--Smith 4.3.16, printed p.618. They include the small
odd fields and do not require a subfield marking of the perfect subgroup.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type*} [Field F] [Finite F]

/-- The faithful inner action preserves triviality of a perfect subgroup’s two-core. -/
theorem odd_perfect_inner_subgroup_twoCore_eq_bot
    (hodd : Odd (Nat.card F))
    (D : Subgroup (MulAut (Group F))) [_root_.Group.IsPerfect D]
    (hi : D ≤ MulAut.innerSubgroup (Group F)) : pCore 2 D = ⊥ := by
  let b := MonoidHom.ofInjective
    (Theory.GroupTheory.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F))
  let f : D →* Group F := b.symm.toMonoidHom.comp (inclusion hi)
  have hf : Function.Injective f := b.symm.injective.comp (inclusion_injective hi)
  have hk := odd_perfect_hom_twoCore_le_ker hodd f
  rw [(MonoidHom.ker_eq_bot_iff _).mpr hf] at hk
  exact bot_unique hk

omit [Finite F] in
/-- The centralizer embeds in the outer quotient because its inner kernel is trivial. -/
theorem inner_image_centralizer_isTwoGroup
    (hout : IsPGroup 2 (MulAut.Outer (Group F)))
    (H : Subgroup (Group F)) [_root_.Group.IsPerfect H] (hne : H ≠ ⊥) :
    IsPGroup 2 (centralizer (H.map (MulAut.conj : Group F →* MulAut (Group F)) :
      Set (MulAut (Group F)))) := by
  rw [Theory.GroupTheory.PerfectSubgroupAutomorphismFixer.inner_centralizer_eq_fixer]
  let C := fixingSubgroup (MulAut (Group F)) (H : Set (Group F))
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Group F))
  apply hout.of_injective (q.comp C.subtype)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hi : (a : MulAut (Group F)) ∈ MulAut.innerSubgroup (Group F) :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨x,hx⟩ := hi
  have hfix := (mem_fixingSubgroup_iff _).mp a.property
  have hc : x ∈ centralizer (H : Set (Group F)) := by
    intro y hy
    have hh := hfix y hy
    rw [←hx] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [centralizer_eq_bot_of_perfect H hne,mem_bot] at hc
  apply mem_bot.mpr
  apply Subtype.ext
  change (a : MulAut (Group F)) = 1
  simpa only [hc,map_one] using hx.symm

/-- In odd field degrees at most two, the full centralizer of a nontrivial
perfect inner subgroup is a two-group. -/
theorem small_degree_perfect_inner_centralizer_isTwoGroup
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hF : Nat.card F = p^e)
    (D : Subgroup (MulAut (Group F))) [_root_.Group.IsPerfect D] (hne : D ≠ ⊥)
    (hi : D ≤ MulAut.innerSubgroup (Group F)) :
    IsPGroup 2 (centralizer (D : Set (MulAut (Group F)))) := by
  let b := MonoidHom.ofInjective
    (Theory.GroupTheory.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F))
  let f : D →* Group F := b.symm.toMonoidHom.comp (inclusion hi)
  have hf (x : D) : MulAut.conj (f x) = (x : MulAut (Group F)) :=
    congrArg (MulAut.innerSubgroup (Group F)).subtype (b.apply_symm_apply (inclusion hi x))
  let H := f.range
  let : _root_.Group.IsPerfect H := _root_.Group.IsPerfect.range _
  have hmap : H.map MulAut.conj = D := by
    ext a
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      rw [hf]
      exact x.property
    · intro ha
      exact ⟨f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,hf ⟨a,ha⟩⟩
  have hnH : H ≠ ⊥ := by
    intro hh
    rw [hh,Subgroup.map_bot] at hmap
    exact hne hmap.symm
  rw [←hmap]
  exact inner_image_centralizer_isTwoGroup
    (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho he hF) H hnH
end Theory.PSL2
