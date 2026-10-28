module

public import Theory.SpecificGroups.SL2.CentralTwoExtensions.Quaternion
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Splitting central two-group extensions of SL₂ over prime fields

In odd characteristic every determinant-one involution in dimension two is
minus the identity. Thus a Sylow two-subgroup is cyclic or generalized
quaternion. A central extension of either kind has trivial derived kernel;
central Sylow transfer then makes the kernel of an arbitrary central
two-group extension disjoint from its ambient derived subgroup.

For p > 3, SL₂(p) is perfect, so the projection restricts to an isomorphism
on the derived subgroup of the extension. Its inverse gives a section of
the original projection. The extension group need not be perfect and the
central two-group kernel can have arbitrary exponent and rank. In particular
p = 5 is included.

This is the two-primary consequence of Aschbacher–Smith I.1.1–3, printed
p.407, and GLS3 §6.1 used by the odd Sp₄ plane-pair argument. The proof uses
only the scalar-involution calculation, the cyclic/quaternion classification,
and transfer; no complete PSL₂ multiplier theorem or torus model is imported.
-/

namespace CentralExtension
open Subgroup

/-- Transfer reduces a central two-kernel to the derived kernel of its Sylow
restriction; cyclic and quaternion Sylow images both have trivial derived kernel. -/
public theorem ker_inf_commutator_eq_bot_of_cyclic_or_quaternion_sylow
    {E B : Type*} [Group E] [Finite E] [Group B] [Finite B]
    (f : E →* B) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (hmodels : ∀ T : Sylow 2 B, IsCyclic T ∨
      ∃ n : ℕ, 0 < n ∧ Nonempty (T ≃* QuaternionGroup n)) :
    f.ker ⊓ _root_.commutator E = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 E := Classical.choice inferInstance
  let T : Sylow 2 B := Sylow.mapSurjective hf S
  let q : S →* T := f.subgroupMap (S : Subgroup E)
  have hq : Function.Surjective q := f.subgroupMap_surjective _
  have hqc : q.ker ≤ center S := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (congrArg Subtype.val hx)) y)
  have hlocal : q.ker ⊓ _root_.commutator S = ⊥ := by
    rcases hmodels T with hcyc | ⟨n, hn, ⟨e⟩⟩
    · let : IsCyclic T := hcyc
      let : IsMulCommutative S := q.isMulCommutative_of_isCyclic_of_ker_le_center hqc
      rw [commutator_eq_bot, inf_bot_eq]
    · let : NeZero n := ⟨hn.ne'⟩
      let g := e.toMonoidHom.comp q
      have hgker : g.ker = q.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
      have hh := ker_inf_commutator_eq_bot_of_quaternion g (e.surjective.comp hq)
        (by rw [hgker]; exact hqc)
      simpa only [hgker] using hh
  apply (f.ker ⊓ _root_.commutator E).eq_bot_iff_forall.mpr
  intro x hx
  have hxS : x ∈ (S : Subgroup E) := hk.le_sylow_of_normal S hx.1
  have hd : x ∈ ⁅(S : Subgroup E), (S : Subgroup E)⁆ :=
    center_inf_commutator_inf_sylow_le_commutator S ⟨⟨hc hx.1, hx.2⟩, hxS⟩
  rw [← map_subtype_commutator] at hd
  obtain ⟨y, hy, hxy⟩ := hd
  have hyeq : y = ⟨x, hxS⟩ := Subtype.ext hxy
  have hmem : (⟨x, hxS⟩ : S) ∈ q.ker ⊓ _root_.commutator S := by
    constructor
    · apply MonoidHom.mem_ker.mpr
      exact Subtype.ext hx.1
    · exact hyeq ▸ hy
  rw [hlocal, mem_bot] at hmem
  exact congrArg Subtype.val hmem

end CentralExtension

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

private theorem eq_neg_one_of_order_two {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (x : SL(2, F)) (hx : orderOf x = 2) : x = -1 := by
  have hpow : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (toGL x).det = 1 := by apply Units.ext; exact x.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (toGL x) (by rw [← map_pow, hpow, map_one]) hd with he | he
  · have hx1 : x = 1 := toGL_injective (by simpa using he)
    simp [hx1] at hx
  · exact Subtype.ext (congrArg Units.val he)

/-- The unique scalar involution makes every Sylow two-subgroup cyclic or
quaternion, without a torus classification or any field-size restriction. -/
public theorem sylow_two_cyclic_or_quaternion {F : Type*} [Field F] [Finite F]
    (hF : (2 : F) ≠ 0) (S : Sylow 2 SL(2, F)) :
    IsCyclic S ∨ ∃ n : ℕ, 0 < n ∧ Nonempty (S ≃* QuaternionGroup n) := by
  classical
  by_cases hc : IsCyclic S
  · exact Or.inl hc
  let : Nontrivial S := Nontrivial.of_not_isCyclic hc
  have hd : 2 ∣ Nat.card S := S.isPGroup'.card_eq_or_dvd.resolve_left
    (ne_of_gt (Finite.one_lt_card : 1 < Nat.card S))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 hd
  have huniq : ∃! z : S, orderOf z = 2 := by
    refine ⟨z, hz, fun x hx => ?_⟩
    apply Subtype.ext
    exact (eq_neg_one_of_order_two hF x ((Subgroup.orderOf_coe x).trans hx)).trans
      (eq_neg_one_of_order_two hF z ((Subgroup.orderOf_coe z).trans hz)).symm
  rcases S.isPGroup'.isCyclic_or_quaternion_of_unique_involution huniq with h | ⟨n, hn, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨2 ^ (n - 2), by positivity, e⟩

/-- Every finite central two-group extension of the actual SL₂(p), p > 3,
splits. The extension group itself need not be perfect. -/
public theorem exists_section_of_central_two_kernel
    {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (f : E →* SL(2, ZMod p))
    (hf : Function.Surjective f) (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker) :
    ∃ s : SL(2, ZMod p) →* E, f.comp s = MonoidHom.id _ := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hsq : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by linear_combination h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  let : Group.IsPerfect SL(2, ZMod p) := ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩
  exact CentralExtension.exists_section_of_ker_inf_commutator_eq_bot f hf
    (CentralExtension.ker_inf_commutator_eq_bot_of_cyclic_or_quaternion_sylow f hf hc hk
      (sylow_two_cyclic_or_quaternion h2))

end Matrix.SpecialLinearGroup
