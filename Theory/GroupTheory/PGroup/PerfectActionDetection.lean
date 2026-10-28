module
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Theory.GroupTheory.PGroup.CriticalSubgroupAutomorphisms
public import Mathlib.GroupTheory.IsPerfect

/-!
# Detecting perfect actions on omega and critical quotients

The restriction kernel on the first omega of a finite abelian p-group is
a p-group. A perfect actor fixing that omega therefore fixes the whole
group. For a characteristic critical subgroup, restriction again has
p-group kernel. If its center is fixed, the combined subgroup-and-quotient
kernel shows that a nontrivial perfect action survives on its central
quotient. All actions are restrictions of the supplied homomorphism.

Source: Thompson's critical-subgroup theorem, Gorenstein, Finite Groups,
Theorem 5.3.11, pp.185--186, and the automorphism kernel argument.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace OmegaAction

theorem perfect_action_eq_one_of_fixes_omega_one
    {A P : Type*} [Group A] [Group.IsPerfect A]
    [Group P] [Finite P] [IsMulCommutative P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (f : A →* MulAut P)
    (hf : ∀ a : A, ∀ x ∈ omega P (p := p) 1, f a x = x) : f = 1 := by
  have hi : f.range ≤ (omegaRestriction P p 1).ker := by
    rintro _ ⟨a,rfl⟩
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (hf a x x.property)
  have hp := (restriction_kernel_isPGroup hP).to_le hi
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsNilpotent f.range := hp.isNilpotent
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  apply MonoidHom.ext
  intro a
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict a) 1)

theorem perfect_centralizes_of_centralizes_omega_one
    {G : Type*} [Group G] (A P : Subgroup G) [Group.IsPerfect A]
    [Finite P] [IsMulCommutative P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hN : A ≤ normalizer (P : Set G))
    (hC : A ≤ centralizer ((omega P (p := p) 1).map P.subtype : Set G)) :
    A ≤ centralizer (P : Set G) := by
  let f := P.normalizerMonoidHom.comp (inclusion hN)
  have hf : f = 1 := perfect_action_eq_one_of_fixes_omega_one hP f (by
    intro a x hx
    apply Subtype.ext
    change (a : G) * x * (a : G)⁻¹ = x
    rw [←hC a.property x (mem_map_of_mem _ hx),mul_inv_cancel_right])
  intro a ha x hx
  have he := congrArg (fun f : A →* MulAut P => (f ⟨a,ha⟩ ⟨x,hx⟩ : G)) hf
  change a * x * a⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end OmegaAction

namespace IsCriticalPSubgroup
private theorem perfect_action_eq_one_of_range_le
    {A P : Type*} [Group A] [Group.IsPerfect A] [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (f : A →* P) (B : Subgroup P)
    (hB : IsPGroup p B) (hf : f.range ≤ B) : f = 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsNilpotent f.range := (hB.to_le hf).isNilpotent
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  apply MonoidHom.ext
  intro a
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict a) 1)

theorem central_quotient_action_ne_one
    {A P : Type*} [Group A] [Group.IsPerfect A] [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {C : Subgroup P} (hC : IsCriticalPSubgroup p C)
    (f : A →* MulAut P) (hne : f ≠ 1)
    (hZ : letI := hC.characteristic
      ∀ (a : A) (z : center C), MulAut.characteristic C (f a) z = z) :
    letI := hC.characteristic
    (quotientAut (center C)).comp ((MulAut.characteristic C).comp f) ≠ 1 := by
  let : C.Characteristic := hC.characteristic
  intro he
  let a := (MulAut.characteristic C).comp f
  have ha : a = 1 := by
    apply perfect_action_eq_one_of_range_le a (automorphismPair (center C)).ker
      (isPGroup_automorphism_pair_kernel _ ((hP.to_subgroup C).to_subgroup _))
    rintro _ ⟨g,rfl⟩
    change automorphismPair (center C) (a g) = 1
    rw [automorphismPair_apply]
    apply Prod.ext
    · apply MulEquiv.ext
      intro z
      exact Subtype.ext (hZ g z)
    · exact DFunLike.congr_fun he g
  apply hne
  apply perfect_action_eq_one_of_range_le f (MulAut.characteristic C).ker
    (C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) (hC.centralizer_eq.le.trans (map_subtype_le _)))
  rintro _ ⟨g,rfl⟩
  exact DFunLike.congr_fun ha g
end IsCriticalPSubgroup
