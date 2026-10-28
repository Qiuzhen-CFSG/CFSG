module

public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Quasithin.EvenCharacteristic

/-!
# Inner subgroups of full Held automorphism normalizers

For a self-normalizing subgroup U of the literal Held carrier, conjugation
identifies U with the inner part of its full automorphism normalizer. Realization
and the bound on the full permutation-normalizer quotient give index one or two.
Lagrange bounds the order, and the normal p-group extension lemma transports
self-centralization of the intrinsic two-core to the full normalizer.

These reductions retain the independent realization and quotient-bound inputs.
Source: the local inspection in Aschbacher--Smith 15.3.41--42, printed p.1138,
and GLS3 Table 5.3p. No local order or core shape is assumed here.
-/

public section
open Subgroup Theory.GroupTheory Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

/-- The inner part of a self-normalizing subgroup's full automorphism normalizer. -/
noncomputable def normalizerInnerEquiv (U : Subgroup Held.He)
    (hU : normalizer (U : Set Held.He) = U) :
    U ≃* (MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U) := by
  let f : U →* (MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U) :=
    { toFun := fun x => ⟨⟨MulAut.conj x.val,
        mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer x.property)⟩, ⟨x.val, rfl⟩⟩
      map_one' := by ext : 2; exact map_one (MulAut.conj : Held.He →* MulAut Held.He)
      map_mul' := fun x y => by ext : 2; exact map_mul (MulAut.conj : Held.He →* MulAut Held.He) x.val y.val }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot
      (congrArg (fun a => a.val.val) h)
  · intro a
    obtain ⟨x, hx⟩ := a.property
    have hn : x ∈ normalizer (U : Set Held.He) :=
      mem_normalizer_iff_map_conj_eq.mpr (hx ▸ a.val.property)
    exact ⟨⟨x, hU ▸ hn⟩, Subtype.ext (Subtype.ext hx)⟩

/-- The realized permutation-normalizer bound controls the full outer index. -/
theorem outer_index_le_two
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    (MulAut.innerSubgroup Held.He).index ≤ 2 :=
  (Nat.card_le_card_of_surjective _
    (normalizerOuterAction_surjective Held.permutationGroup hreal)).trans hbound

/-- Every automorphism normalizer has inner index dividing two. -/
theorem normalizer_inner_index_dvd_two (U : Subgroup Held.He)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    ((MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U)).index ∣ 2 := by
  have hd := relIndex_dvd_index_of_normal (MulAut.innerSubgroup Held.He)
    (automorphismNormalizer U)
  have hi := outer_index_le_two hreal hbound
  have hp := Nat.pos_of_ne_zero (MulAut.innerSubgroup Held.He).index_ne_zero_of_finite
  have h12 : (MulAut.innerSubgroup Held.He).index = 1 ∨
      (MulAut.innerSubgroup Held.He).index = 2 := by omega
  exact hd.trans (h12.elim (fun h => h ▸ one_dvd _) (fun h => h ▸ dvd_rfl))

/-- Self-normalization identifies the inner part, bounding the full normalizer order. -/
theorem automorphismNormalizer_card_dvd_twice (U : Subgroup Held.He)
    (hU : normalizer (U : Set Held.He) = U)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    Nat.card (automorphismNormalizer U) ∣ Nat.card U * 2 := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U)
  have he := Nat.card_congr (normalizerInnerEquiv U hU).toEquiv
  rw [← I.card_mul_index, he]
  exact Nat.mul_dvd_mul_left _ (normalizer_inner_index_dvd_two U hreal hbound)

/-- Characteristic two passes from the self-normalizing inner subgroup to its
full automorphism normalizer through the normal two-group extension. -/
theorem automorphismNormalizer_characteristic_two (U : Subgroup Held.He)
    (hU : normalizer (U : Set Held.He) = U)
    (hc : centralizer (pCore 2 U : Set U) ≤ pCore 2 U)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    generalizedFitting (automorphismNormalizer U) = pCore 2 (automorphismNormalizer U) := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U)
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_le_of_normal_pGroup_quotient I
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (normalizerInnerEquiv U hU)).mp hc
  · apply IsPGroup.of_card_dvd_pow (n := 1)
    exact normalizer_inner_index_dvd_two U hreal hbound
end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
