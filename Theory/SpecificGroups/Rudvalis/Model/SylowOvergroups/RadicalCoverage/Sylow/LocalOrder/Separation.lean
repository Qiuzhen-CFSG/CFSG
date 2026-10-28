module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Maps
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Decoder

/-!
# Separation of the 16384 binary products

The images of points 0 and 1 distinguish the original candidate normal
forms. A packed two-stage decoder supplies a left inverse; its equation is
checked by kernel reduction for every index. This proves the lower bound
without assuming collection, a subgroup order, or an ambient group order.

The data and the left-action convention come from the preserved ATLAS
degree-4060 representation; see `Candidate.lean` and `source/Generate.py`.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

private theorem allIndices (P : Fin 16384 → Prop) [DecidablePred P]
    (h : Rudvalis.Data.checkNat
      (fun k => decide (P ⟨k % 16384, Nat.mod_lt _ (by decide)⟩)) 16384 = true) :
    ∀ i, P i := by
  have hcheck (f : Nat → Bool) (n : Nat) :
      Rudvalis.Data.checkNat f n = true → ∀ k < n, f k = true := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Rudvalis.Data.checkNat, Bool.and_eq_true]
      rintro ⟨hn, hfn⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact ih hn k hlt
      · exact hfn
  rintro ⟨k, hk⟩
  have hp := of_decide_eq_true (hcheck _ _ h k hk)
  simpa only [Nat.mod_eq_of_lt hk] using hp

set_option maxRecDepth 60000 in
private theorem decode_normalMap :
    ∀ n : Fin 16384, decode (normalMap n 0) (normalMap n 1) = n.val := by
  apply allIndices
  decide +kernel

/-- The original binary products are distinct in the original model. -/
public theorem normalForm_injective : Function.Injective candidateNormalForm := by
  intro i j h
  apply Fin.ext
  have h0 := congrArg (fun g : Model => g • (0 : Fin 4060)) h
  have h1 := congrArg (fun g : Model => g • (1 : Fin 4060)) h
  rw [normal_smul, normal_smul] at h0 h1
  rw [← decode_normalMap i, ← decode_normalMap j, h0, h1]

/-- All 16384 distinct products lie in the candidate. -/
public theorem candidate_card_lower : 16384 ≤ Nat.card candidate := by
  let f : Fin 16384 → candidate := fun n => ⟨candidateNormalForm n, candidateNormalForm_mem n⟩
  have hf : Function.Injective f := fun _ _ h =>
    normalForm_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
