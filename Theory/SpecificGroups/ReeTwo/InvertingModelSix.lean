module
public import Theory.SpecificGroups.ReeTwo.InvertingModelSixCounts

/-!
# Automorphisms fix the marked involution in both action-six first cores

The intrinsic first core has center of order four. Every square root of the
mark has centralizer order 128. Each other nonidentity central element has an
explicit square root with centralizer order 256. These intrinsic invariants
force every automorphism to fix the mark, for either actor fourth power.

Source: the Shinoda (1975), (2.3), coordinate model and the finite certificates
in `InvertingModelSixStructure` and `InvertingModelSixCounts`.
-/

namespace ReeTwo.InvertingModel
open Six

/-- Both choices of the actor's fourth power in the sixth census action have
an automorphism-invariant marked involution in their intrinsic first core. -/
public theorem six_fixed (ε : Bool) (a : MulAut (firstCore 6 ε)) :
    a (centralInvolution 6 ε) = centralInvolution 6 ε := by
  apply Group.fixed_of_square_root_commutingCard (centralInvolution 6 ε) 128
    (centralInvolution_mem_center 6 ε) (centralInvolution_ne_one 6 ε)
    (square_root_commutingCard ε) _ a
  intro x hx hx1 hxz
  rcases firstCore_center_cases ε x hx with h | h | h | h
  · exact False.elim (hx1 (Subtype.ext h))
  · refine ⟨inside ε (root ε 1) rfl, ?_, ?_⟩
    · apply Subtype.ext
      change (root ε 1) ^ 2 = x.val
      rw [h]
      exact (by decide +kernel : ∀ ε : Bool, root ε 1 ^ 2 = root ε 5) ε
    · rw [commutingCard_eq]
      change count (root ε 1) ≠ 128
      rw [(witness_counts ε).1]
      decide
  · exact False.elim (hxz (Subtype.ext h))
  · refine ⟨inside ε (witness ε) rfl, ?_, ?_⟩
    · apply Subtype.ext
      change witness ε ^ 2 = x.val
      rw [h]
      exact (by decide +kernel : ∀ ε : Bool, witness ε ^ 2 = root ε 5 * root ε 9) ε
    · rw [commutingCard_eq]
      change count (witness ε) ≠ 128
      rw [(witness_counts ε).2]
      decide

end ReeTwo.InvertingModel
