module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder

/-!
# Completeness of the Rudvalis candidate normal forms

The 16384 binary products are distinct and lie in the candidate subgroup,
whose order is 16384. The resulting injection is therefore surjective.
This supplies actual normal-form witnesses for arbitrary candidate elements.

Source: the ATLAS degree-4060 action and preserved `RuG1-max4W1` program;
the word conventions and attribution are in `Sylow.Candidate`.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate

/-- Every element of the candidate has one of the certified binary normal forms. -/
public theorem exists_candidateNormalForm {x : Model} (hx : x ∈ candidate) :
    ∃ n : Fin 16384, candidateNormalForm n = x := by
  let f : Fin 16384 → candidate := fun n => ⟨candidateNormalForm n, candidateNormalForm_mem n⟩
  have hi : Function.Injective f := fun _ _ h =>
    LocalOrder.normalForm_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f :=
    (hi.bijective_of_nat_card_le (by rw [candidate_card, Nat.card_fin])).2
  obtain ⟨n, hn⟩ := hs ⟨x, hx⟩
  exact ⟨n, congrArg Subtype.val hn⟩

end Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
