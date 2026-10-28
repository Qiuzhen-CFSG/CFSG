module
public import Theory.GroupAction.CoprimeMovingQuotient
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
/-!
# Coprime centralizer splitting through the actual action image

The conjugation image may have coprime order even when the whole acting
subgroup does not. Replacing the actor by its actual image preserves the
fixed and displacement subgroups, so the usual coprime splitting applies.
The source15.3.18 consumer uses the odd orthogonal image of Y_L on V.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem commutator_disjoint_centralizer_of_actionRange_coprime
    (V A : Subgroup G) [IsMulCommutative V]
    (hn : A ≤ normalizer (V : Set G))
    (hc : Nat.Coprime
      (Nat.card (V.normalizerMonoidHom.comp (inclusion hn)).range) (Nat.card V)) :
    Disjoint ⁅V,A⁆ (V ⊓ centralizer (A : Set G)) := by
  let f := V.normalizerMonoidHom.comp (inclusion hn)
  let α : f.range →* MulAut V := f.range.subtype
  let _ : MulDistribMulAction f.range V := MulDistribMulAction.compHom V α
  let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V f.rangeRestrict
  have hs : Group.IsSolvable V := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hd := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := f.range) hs hc inferInstance
  have he := Theory.GroupAction.commutatorAction_eq_of_actor_surjective (V := V) f.rangeRestrict
    f.rangeRestrict_surjective
  have hfix : fixedPointSubgroup f.range V = fixedPointSubgroup A V := by
    ext v
    constructor
    · intro h a
      exact h (f.rangeRestrict a)
    · intro h a
      obtain ⟨a,rfl⟩ := f.rangeRestrict_surjective a
      exact h a
  rw [hfix,←he] at hd
  have hm := Subgroup.disjoint_map V.subtype_injective hd.symm.disjoint
  have hcomm : (commutatorAction A V).map V.subtype = ⁅V,A⁆ := by
    let _ : Normalizes A V := ⟨hn⟩
    exact commutatorAction_subgroup_conj_map_eq_commutator V A hn
  have hcent : (fixedPointSubgroup A V).map V.subtype = V ⊓ centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      refine ⟨v.property,mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have he := congrArg Subtype.val (hv ⟨a,ha⟩)
      change a*(v:G)*a⁻¹=(v:G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · rintro ⟨hxV,hxC⟩
      refine ⟨⟨x,hxV⟩,?_,rfl⟩
      intro a
      apply Subtype.ext
      change (a:G)*x*(a:G)⁻¹=x
      rw [(mem_centralizer_iff.mp hxC) a a.property,mul_inv_cancel_right]
  rwa [hcomm,hcent] at hm
end Subgroup
