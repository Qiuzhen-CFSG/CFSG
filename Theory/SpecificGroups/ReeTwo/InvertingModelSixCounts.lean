module
public import Theory.SpecificGroups.ReeTwo.InvertingModelSixCounting

/-!
# Finite square-root centralizer checks for action six

The two central coordinates contribute a factor of four. Kernel-checked
counts on the remaining 512 representatives distinguish the last root from
the other central involutions, for both fourth-power choices.
Source: the verified Shinoda coordinates and `InvertingModelSixCounting`.
-/

@[expose] public section
namespace ReeTwo.InvertingModel.Six

def witness (ε : Bool) : Model 6 ε := ⟨Core.CensusPacked.decode 259, 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem witness_counts : ∀ ε : Bool, count (root ε 1) = 256 ∧ count (witness ε) = 256 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem reduced_square_count_packed : ∀ (ε : Bool) (p : ReducedParams),
    pmul ε (code (reducedElt ε p)) (code (reducedElt ε p)) = 512 → count (reducedElt ε p) = 128 := by
  decide +kernel

theorem reduced_square_count (ε : Bool) (p : ReducedParams) :
    cmul (reducedElt ε p) (reducedElt ε p) = root ε 9 → count (reducedElt ε p) = 128 := by
  have h := reduced_square_count_packed ε p
  change pmul ε (code (reducedElt ε p)) (code (reducedElt ε p)) = code (root ε 9) → _ at h
  simpa only [pmul_code, code_injective.eq_iff, cmul_eq] using h

theorem square_root_commutingCard (ε : Bool) (x : firstCore 6 ε)
    (hx : x ^ 2 = centralInvolution 6 ε) : Group.commutingCard x = 128 := by
  let p := parameterEquiv ε x
  let r := inside ε (reducedElt ε (reduceParam p)) rfl
  let c := centerWord ε p.1.2.2.2.2.1 p.1.2.2.2.2.2.2.2.2
  have he : elt ε p = x.val := congrArg Subtype.val ((parameterEquiv ε).symm_apply_apply x)
  have hd : x = r * c := by
    apply Subtype.ext
    change x.val = reducedElt ε (reduceParam p) * centerElt ε _ _
    simpa only [cmul_eq, he] using decomposition ε p
  have hc : c ∈ Subgroup.center (firstCore 6 ε) := centerWord_mem_center _ _ _
  have hsq : r ^ 2 = centralInvolution 6 ε := by
    rw [hd, (show Commute r c from Subgroup.mem_center_iff.mp hc r).mul_pow,
      centerWord_square, mul_one] at hx
    exact hx
  rw [hd, commutingCard_mul_center r c hc, commutingCard_eq]
  apply reduced_square_count
  rw [cmul_eq]
  have hv := congrArg (firstCore 6 ε).subtype hsq
  rw [map_pow] at hv
  change reducedElt ε (reduceParam p) ^ 2 = root ε 9 at hv
  simpa only [pow_two] using hv

end ReeTwo.InvertingModel.Six
