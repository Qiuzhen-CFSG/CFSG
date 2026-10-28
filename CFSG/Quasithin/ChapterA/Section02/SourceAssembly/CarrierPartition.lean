module
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.Models
public import CFSG.Quasithin.ChapterA.Section02.OddLie.Models
/-!
# Exhaustive source partition of the full known-simple catalogue

Each classical and exceptional coefficient field has positive prime-power
order. Splitting its defining prime into two or an odd prime routes its
literal model to the even or odd source families. Prime cyclic, alternating
and all twenty-six sporadic carriers remain their original alternatives;
all conventional small derived carriers belong to the even source list.
No order, simplicity or rank theorem is assumed for this partition.
Source: the full GLS3 Theorem 2.2.7 catalogue and Aschbacher–Smith A.2.16–19.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02
open KnownSimple
universe u
variable {G : Type u} [Group G]

private theorem classical_partition (h : IsClassicalModel G) :
    EvenLie.IsEvenLieCarrier G ∨ OddLie.IsOddLieCarrier G := by
  cases h with
  | linear d q hp hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hp.1
    by_cases h2 : r = 2
    · subst r
      exact .inl (.linear d e he hp hm)
    · exact .inr (.linear d r e hr (hr.odd_of_ne_two h2) he hp hm)
  | unitary d q hp hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hp.1
    by_cases h2 : r = 2
    · subst r
      exact .inl (.unitary d e he hp hm)
    · exact .inr (.unitary d r e hr (hr.odd_of_ne_two h2) he hp hm)
  | symplectic d q hp hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hp.1
    by_cases h2 : r = 2
    · subst r
      exact .inl (.symplectic d e he hp hm)
    · exact .inr (.symplectic d r e hr (hr.odd_of_ne_two h2) he hp hm)
  | orthogonalPlus d q hp hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hp.1
    by_cases h2 : r = 2
    · subst r
      exact .inl (.orthogonalPlus d e he hp hm)
    · exact .inr (.orthogonalPlus d r e hr (hr.odd_of_ne_two h2) he hp hm)
  | orthogonalOdd d q hp hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hp.1
    by_cases h2 : r = 2
    · subst r
      exact .inl (.orthogonalOdd d e he hp hm)
    · exact .inr (.orthogonalOdd d r e hr (hr.odd_of_ne_two h2) he hp hm)
  | orthogonalMinus d q hp hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hp.1
    by_cases h2 : r = 2
    · subst r
      exact .inl (.orthogonalMinus d e he hp hm)
    · exact .inr (.orthogonalMinus d r e hr (hr.odd_of_ne_two h2) he hp hm)

private theorem exceptional_partition (h : IsExceptionalExtensionModel G) :
    EvenLie.IsEvenLieCarrier G ∨ OddLie.IsOddLieCarrier G := by
  cases h with
  | reeG2 q hm => exact .inr (.ree q hm)
  | f4 q hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hm.parameter_isPrimePow
    by_cases h2 : r = 2
    · subst r
      exact .inl (.f4 e he hm)
    · exact .inr (.f4 r e hr (hr.odd_of_ne_two h2) he hm)
  | e6 q hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hm.parameter_isPrimePow
    by_cases h2 : r = 2
    · subst r
      exact .inl (.e6 e he hm)
    · exact .inr (.e6 r e hr (hr.odd_of_ne_two h2) he hm)
  | e7 q hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hm.parameter_isPrimePow
    by_cases h2 : r = 2
    · subst r
      exact .inl (.e7 e he hm)
    · exact .inr (.e7 r e hr (hr.odd_of_ne_two h2) he hm)
  | e8 q hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hm.parameter_isPrimePow
    by_cases h2 : r = 2
    · subst r
      exact .inl (.e8 e he hm)
    · exact .inr (.e8 r e hr (hr.odd_of_ne_two h2) he hm)
  | twistedE6 q hm =>
    obtain ⟨r,e,hr,he,rfl⟩ := (isPrimePow_nat_iff q).mp hm.parameter_isPrimePow
    by_cases h2 : r = 2
    · subst r
      exact .inl (.twistedE6 e he hm)
    · exact .inr (.twistedE6 r e hr (hr.odd_of_ne_two h2) he hm)

theorem knownCarrier_source_partition (h : IsKnownSimpleCarrier G) :
    IsPrimeCyclicCarrier G ∨ (∃ n, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      EvenLie.IsEvenLieCarrier G ∨ OddLie.IsOddLieCarrier G ∨ IsSporadicCarrier G := by
  cases h with
  | cyclic hm => exact .inl hm
  | alternating n hn hm => exact .inr (.inl ⟨n,hn,hm⟩)
  | classical hm =>
    rcases classical_partition hm with he | ho
    · exact .inr (.inr (.inl he))
    · exact .inr (.inr (.inr (.inl ho)))
  | exceptional hm =>
    rcases exceptional_partition hm with he | ho
    · exact .inr (.inr (.inl he))
    · exact .inr (.inr (.inr (.inl ho)))
  | suzuki m hm iso => exact .inr (.inr (.inl (.suzuki m hm iso)))
  | smallDerived hm => exact .inr (.inr (.inl (.smallDerived hm)))
  | sporadic hm => exact .inr (.inr (.inr (.inr hm)))
  | reeF4 hm =>
    obtain ⟨m,hm,iso⟩ := hm
    exact .inr (.inr (.inl (.reeF4 m hm iso)))
  | triality hm =>
    obtain ⟨P,iso⟩ := hm
    by_cases h2 : P.prime = 2
    · apply Or.inr; apply Or.inr; apply Or.inl
      exact .triality P.exponent P.exponent_pos ⟨P,by simp [Triality.Standard.Parameters.q,h2],iso⟩
    · exact .inr (.inr (.inr (.inl (.triality P (P.prime_prime.odd_of_ne_two h2) iso))))
  | g2 hm =>
    obtain ⟨F,hF,hfin,hcard,iso⟩ := hm
    let := Fintype.ofFinite F
    have hq : IsPrimePow (Nat.card F) := by
      simpa only [Nat.card_eq_fintype_card] using FiniteField.isPrimePow_card F
    obtain ⟨r,e,hr,he,hre⟩ := (isPrimePow_nat_iff _).mp hq
    have model : ClassificationModels.IsG2At G (r^e) := ⟨F,hF,hfin,hre.symm,iso⟩
    by_cases h2 : r = 2
    · subst r
      have he2 : 2 ≤ e := by
        by_contra hh
        have he1 : e = 1 := by omega
        simp only [he1, pow_one] at hre
        omega
      exact .inr (.inr (.inl (.g2 e he2 model)))
    · exact .inr (.inr (.inr (.inl (.g2 r e hr (hr.odd_of_ne_two h2) he model))))
end CFSG.Quasithin.ChapterA.Section02
