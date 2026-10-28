module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Steps1

/-!
# The last three covers and the encoded order bound

The remaining factors 4, 4, 3 end in the monoid with no generators, of order
one. Combining the five checked covers gives the upper bound 967680.
Source application: AS I.1.3(6), GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate

theorem step2 (i : Fin 6) (r : Fin 4) :
    gen2 i * rep2 r = rep2 (act2 i r) * word gen3 (factor2 i r) := by
  fin_cases i
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen2 0 * rep2 r)
      (fun r : Fin 4 => rep2 (act2 0 r) * word gen3 (factor2 0 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen2 1 * rep2 r)
      (fun r : Fin 4 => rep2 (act2 1 r) * word gen3 (factor2 1 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen2 2 * rep2 r)
      (fun r : Fin 4 => rep2 (act2 2 r) * word gen3 (factor2 2 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen2 3 * rep2 r)
      (fun r : Fin 4 => rep2 (act2 3 r) * word gen3 (factor2 3 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen2 4 * rep2 r)
      (fun r : Fin 4 => rep2 (act2 4 r) * word gen3 (factor2 4 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen2 5 * rep2 r)
      (fun r : Fin 4 => rep2 (act2 5 r) * word gen3 (factor2 5 r))
      (by decide +kernel) r

theorem card2_le : Nat.card (Submonoid.closure (Set.range gen2)) ≤
    4 * Nat.card (Submonoid.closure (Set.range gen3)) :=
  closure_card_le gen2 gen3 rep2 act2 factor2 0 rfl step2

theorem step3 (i : Fin 4) (r : Fin 4) :
    gen3 i * rep3 r = rep3 (act3 i r) * word gen4 (factor3 i r) := by
  fin_cases i
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen3 0 * rep3 r)
      (fun r : Fin 4 => rep3 (act3 0 r) * word gen4 (factor3 0 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen3 1 * rep3 r)
      (fun r : Fin 4 => rep3 (act3 1 r) * word gen4 (factor3 1 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen3 2 * rep3 r)
      (fun r : Fin 4 => rep3 (act3 2 r) * word gen4 (factor3 2 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 4 => gen3 3 * rep3 r)
      (fun r : Fin 4 => rep3 (act3 3 r) * word gen4 (factor3 3 r))
      (by decide +kernel) r

theorem card3_le : Nat.card (Submonoid.closure (Set.range gen3)) ≤
    4 * Nat.card (Submonoid.closure (Set.range gen4)) :=
  closure_card_le gen3 gen4 rep3 act3 factor3 0 rfl step3

theorem step4 (i : Fin 2) (r : Fin 3) :
    gen4 i * rep4 r = rep4 (act4 i r) * word gen5 (factor4 i r) := by
  fin_cases i
  · exact eq_of_checkFamily
      (fun r : Fin 3 => gen4 0 * rep4 r)
      (fun r : Fin 3 => rep4 (act4 0 r) * word gen5 (factor4 0 r))
      (by decide +kernel) r
  · exact eq_of_checkFamily
      (fun r : Fin 3 => gen4 1 * rep4 r)
      (fun r : Fin 3 => rep4 (act4 1 r) * word gen5 (factor4 1 r))
      (by decide +kernel) r

theorem card4_le : Nat.card (Submonoid.closure (Set.range gen4)) ≤
    3 * Nat.card (Submonoid.closure (Set.range gen5)) :=
  closure_card_le gen4 gen5 rep4 act4 factor4 0 rfl step4

theorem card5 : Nat.card (Submonoid.closure (Set.range gen5)) = 1 := by
  have he : Submonoid.closure (Set.range gen5) = (⊥ : Submonoid M) := by
    apply le_antisymm _ bot_le
    apply Submonoid.closure_le.mpr
    rintro g ⟨i, _⟩
    exact Fin.elim0 i
  rw [he]
  let : Subsingleton (⊥ : Submonoid M) := ⟨fun a b =>
    Subtype.ext ((Submonoid.mem_bot.mp a.property).trans
      (Submonoid.mem_bot.mp b.property).symm)⟩
  exact Nat.card_unique

theorem encoded_card_le : Nat.card (Submonoid.closure (Set.range gen0)) ≤ 967680 := by
  have h0 := card0_le
  have h1 := card1_le
  have h2 := card2_le
  have h3 := card3_le
  have h4 := card4_le
  have h5 := card5
  omega

end Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate
