module

public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.FixedPoints
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.CoreCriterion

/-!
# Order and two-core of the first M₁₂ parabolic

Sharp five-transitivity gives the upper bound 192. The embedded quaternion
product lies in the kernel of the matching action, whose image has order six.
Its order 32 forces equality in the bound and identifies it with the kernel,
and hence with the two-core.
Source: Aschbacher–Smith, Lemma 14.2.21.
-/

@[expose] public section
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M12SmallPair.FirstCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

def fivePoints : Fin 5 ↪ Fin 12 := ⟨![2,7,9,0,1], by decide +kernel⟩

theorem fixedPointAction_spec (g : firstParabolic) (i : Fin 4) :
    (g : M12).val (fixedLabel i) = fixedLabel (fixedPointAction g i) :=
  restrictAction_spec secondRepresentation fixedLabel fixedLabel_injective second_stable g i

abbrev movedPoints := {i : Fin 12 // zPerm i ≠ i}

def firstEncoding (g : firstParabolic) : Equiv.Perm (Fin 4) × movedPoints :=
  (fixedPointAction g, ⟨(g : M12).val 1, by
    intro heq
    have hc := Subgroup.mem_centralizer_singleton_iff.mp g.property
    have h := congrArg (fun x : M12 => x.val 1) hc
    change (g : M12).val (zPerm 1) = zPerm ((g : M12).val 1) at h
    rw [heq] at h
    have hf := (g : M12).val.injective h
    exact (by decide +kernel : zPerm 1 ≠ 1) hf⟩)

theorem firstEncoding_injective : Function.Injective firstEncoding := by
  intro g h heq
  apply Subtype.ext
  apply m12_isSharplyFivePretransitive.bijective_orbitMap fivePoints |>.injective
  apply Function.Embedding.ext
  intro i
  have hf := congrArg Prod.fst heq
  have hm := congrArg (fun p => p.2.val) heq
  have hs (j : Fin 4) : (g : M12).val (fixedLabel j) = (h : M12).val (fixedLabel j) := by
    rw [fixedPointAction_spec, fixedPointAction_spec]
    exact congrArg fixedLabel (congrArg (fun p : Equiv.Perm (Fin 4) => p j) hf)
  fin_cases i
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · exact hm

theorem card_firstParabolic_le : Nat.card firstParabolic ≤ 192 := by
  have h := Nat.card_le_card_of_injective firstEncoding firstEncoding_injective
  have hc : Nat.card movedPoints = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, hc] at h
  norm_num [Nat.factorial] at h
  exact h

theorem core_le_matching_ker : core.subgroupOf firstParabolic ≤ matchingQuotient.ker := by
  intro g hg
  obtain ⟨q,r,hr⟩ := (mem_core g.val).mp hg
  have h : ∀ q r : QuaternionGroup 2, ∃ σ : Equiv.Perm (Fin 4),
      (∀ i, (leftEmbedding q * rightEmbedding r).val (fixedLabel i) = fixedLabel (σ i)) ∧
      (∀ j, σ * matchingLabel j * σ⁻¹ = matchingLabel j) := by decide +kernel
  obtain ⟨σ,hσ,hmatch⟩ := h q r
  apply MonoidHom.mem_ker.mpr
  change matchingAction (fixedPointAction g) = 1
  have hf : fixedPointAction g = σ := by
    apply second_four_action_eq
    intro i
    change g.val.val (fixedLabel i) = fixedLabel (σ i)
    rw [← hr]
    exact hσ i
  rw [hf]
  exact matching_action_eq σ 1 hmatch

theorem card_core_subgroupOf : Nat.card (core.subgroupOf firstParabolic) = 32 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe core_le_firstParabolic).toEquiv]
  exact card_core

theorem card_matching_ker : Nat.card matchingQuotient.ker = 32 := by
  have hlo := Subgroup.card_le_of_le core_le_matching_ker
  rw [card_core_subgroupOf] at hlo
  have hmul := matchingQuotient.ker.card_mul_index
  rw [Subgroup.index_ker, matchingQuotient.range_eq_top_of_surjective
    matchingQuotient_surjective, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at hmul
  norm_num [Nat.factorial] at hmul
  change Nat.card matchingQuotient.ker * 6 = Nat.card firstParabolic at hmul
  have hbound := card_firstParabolic_le
  omega

theorem core_eq_matching_ker : core.subgroupOf firstParabolic = matchingQuotient.ker :=
  Subgroup.eq_of_le_of_card_ge core_le_matching_ker
    (by rw [card_matching_ker, card_core_subgroupOf])

end
end Sporadic.Mathieu.M12SmallPair.FirstCore

namespace Sporadic.Mathieu.M12SmallPair
open FirstCore

theorem card_firstParabolic : Nat.card firstParabolic = 192 := by
  have hmul := matchingQuotient.ker.card_mul_index
  rw [Subgroup.index_ker, matchingQuotient.range_eq_top_of_surjective
    matchingQuotient_surjective, Subgroup.card_top, Nat.card_perm, Nat.card_fin,
    card_matching_ker] at hmul
  norm_num [Nat.factorial] at hmul
  exact hmul.symm

theorem core_subgroupOf_eq_pCore : core.subgroupOf firstParabolic = pCore 2 firstParabolic :=
  FirstCore.core_eq_matching_ker.trans
    (FirstCore.core_eq_ker_of_surjective_perm_three card_firstParabolic
      FirstCore.matchingQuotient FirstCore.matchingQuotient_surjective).symm

theorem mapped_pCore_eq_core : (pCore 2 firstParabolic).map firstParabolic.subtype = core := by
  rw [← core_subgroupOf_eq_pCore]
  exact Subgroup.map_subgroupOf_eq_of_le core_le_firstParabolic

instance core_normal_firstParabolic : (core.subgroupOf firstParabolic).Normal := by
  rw [core_subgroupOf_eq_pCore]
  infer_instance

/-- The quotient is the actual permutation action on the three matchings. -/
noncomputable def firstParabolicCoreQuotient :
    firstParabolic ⧸ core.subgroupOf firstParabolic ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq FirstCore.core_eq_matching_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective FirstCore.matchingQuotient
      FirstCore.matchingQuotient_surjective)

end Sporadic.Mathieu.M12SmallPair
