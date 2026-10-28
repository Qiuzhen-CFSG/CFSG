module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# Detecting Sylow-preserving actions on a Sylow subgroup

If a Sylow two-subgroup is self-normalizing and the outer automorphism
group is a two-group, every action preserving that Sylow has two-group
image. A power of two makes each actor inner, and its conjugating element
then lies in the Sylow. A Sylow subgroup of any finite acting group
therefore induces the entire action image.

Self-normalization also passes to a direct square by projecting its Sylow
subgroup to the two factors. Source application: Aschbacher--Smith 10.2.5,
printed p.748, the odd-prime full-intersection normalizer case.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SylowNormalizerAction
variable {Q A : Type*} [Group Q] [Group A]

/-- A Sylow-preserving action has two-group image when both its inner and outer parts do. -/
theorem action_two_of_self_normalizing_sylow
    (S : Sylow 2 Q) (hN : normalizer (S : Set Q) = (S : Subgroup Q))
    (ho : IsPGroup 2 (MulAut.Outer Q)) (f : A →* MulAut Q)
    (hf : ∀ a, (S : Subgroup Q).map (f a).toMonoidHom = S) : IsPGroup 2 f.range := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  rintro ⟨a, b, rfl⟩
  obtain ⟨k,hk⟩ := ho (QuotientGroup.mk' (MulAut.innerSubgroup Q) (f b))
  have hi : (f b) ^ 2 ^ k ∈ MulAut.innerSubgroup Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (MulAut.innerSubgroup Q)) ((f b) ^ 2 ^ k) = 1
    rw [map_pow]
    exact hk
  obtain ⟨x,hx⟩ := hi
  have hxS : x ∈ (S : Subgroup Q) := by
    rw [← hN]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hx, ← map_pow]
    exact hf (b ^ 2 ^ k)
  obtain ⟨m,hm⟩ := S.isPGroup' (⟨x,hxS⟩ : S)
  refine ⟨k+m,?_⟩
  apply Subtype.ext
  change (f b) ^ 2 ^ (k+m) = 1
  rw [pow_add,pow_mul,←hx,←map_pow]
  have hxone : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [hxone,map_one]

variable [Finite A]
/-- Every image element of a two-group action is induced by the specified Sylow. -/
theorem action_detected_on_sylow (T : Sylow 2 A) (f : A →* Q)
    (hf : IsPGroup 2 f.range) (a : A) :
    ∃ t ∈ (T : Subgroup A), f t = f a := by
  let S := T.mapSurjective f.rangeRestrict_surjective
  have hS : (S : Subgroup f.range) = ⊤ :=
    (S.is_maximal' (hf.to_subgroup ⊤) le_top).symm
  have ha : f.rangeRestrict a ∈ (S : Subgroup f.range) := hS.symm ▸ mem_top _
  obtain ⟨t,ht,he⟩ := ha
  exact ⟨t,ht,congrArg Subtype.val he⟩

/-- Self-normalization of every factor Sylow passes to the direct square. -/
theorem product_sylow_self_normalizing [Finite Q]
    (hN : ∀ S : Sylow 2 Q, normalizer (S : Set Q) = (S : Subgroup Q))
    (S : Sylow 2 (Q × Q)) : normalizer (S : Set (Q × Q)) = (S : Subgroup (Q × Q)) := by
  let U := S.mapSurjective (f := MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩)
  let V := S.mapSurjective (f := MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩)
  have he : (S : Subgroup (Q × Q)) = (U : Subgroup Q).prod (V : Subgroup Q) := by
    symm
    apply S.is_maximal'
    · obtain ⟨a,ha⟩ := U.isPGroup'.exists_card_eq
      obtain ⟨b,hb⟩ := V.isPGroup'.exists_card_eq
      apply IsPGroup.of_card (n := a+b)
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
      rw [ha,hb,pow_add]
    · intro x hx
      exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
  change normalizer ((S : Subgroup (Q × Q)) : Set (Q × Q)) = _
  apply le_antisymm _ (S : Subgroup (Q × Q)).le_normalizer
  intro x hx
  rw [he]
  have hfirst := le_normalizer_map (MonoidHom.fst Q Q) (mem_map_of_mem _ hx)
  have hsecond := le_normalizer_map (MonoidHom.snd Q Q) (mem_map_of_mem _ hx)
  exact ⟨(hN U) ▸ hfirst, (hN V) ▸ hsecond⟩

end Theory.GroupTheory.SylowNormalizerAction
