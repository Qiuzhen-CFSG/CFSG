module
public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import ABG.ChapterII.Section3.QOddCoreQuotient
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Characteristic power in the odd-core quotient

The source characteristic-power datum of a finite group passes unchanged
to its odd-core quotient. Together with the proved preservation of the
Q-group predicate, this is Alperin--Brauer--Gorenstein, Chapter II,
Section 3, Lemma 1 (article page 23).

Write X = G/O(G). The datum supplies an actual characteristic SL2 subgroup
in X. Since O(X) is trivial, quotienting by it gives a group canonically
isomorphic to X. Map the characteristic subgroup through this equivalence
and transport its SL2 model, keeping the same finite field and cardinality.
The proof uses the existing characteristic-image transport helper; it does
not replace characteristicity with normality or change the source predicate.
The final wrapper pairs this datum with the actual enlarged Q-group quotient
result, without adding a Sylow-shape hypothesis to the data-only theorem.
-/

namespace ABG
universe u

/-- The characteristic constituent datum survives quotienting by the odd core. -/
public theorem HasSourceQCharacteristicPower.oddCore_quotient
    {G : Type u} [Group G] [Finite G] {q : ℕ}
    (h : HasSourceQCharacteristicPower G q) :
    HasSourceQCharacteristicPower (G ⧸ pPrimeCore 2 G) q := by
  obtain ⟨F, iF, fF, hF, hq, L, hL, ⟨eL⟩⟩ := h
  let : Field F := iF
  let : Finite F := fF
  let X := G ⧸ pPrimeCore 2 G
  let e : X ≃* (X ⧸ pPrimeCore 2 X) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) 2).symm)
  exact ⟨F, iF, fF, hF, hq, L.map e.toMonoidHom, characteristic_map_equiv e L hL,
    ⟨(Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm.trans eL⟩⟩

/-- ABG II.3 Lemma 1: the odd-core quotient is a Q-group of the same power. -/
public theorem IsQGroup.oddCore_quotient_characteristicPower
    {G : Type u} [Group G] [Finite G] {q : ℕ}
    (hG : IsQGroup G) (hq : HasSourceQCharacteristicPower G q) :
    IsQGroup (G ⧸ pPrimeCore 2 G) ∧
      HasSourceQCharacteristicPower (G ⧸ pPrimeCore 2 G) q :=
  ⟨hG.oddCore_quotient, hq.oddCore_quotient⟩

end ABG

