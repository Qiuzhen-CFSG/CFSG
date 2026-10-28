module

public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import ABG.ChapterII.Section3.QOddCoreQuotient
public import ABG.ChapterII.Section2.SylowShapeTransport
public import ABG.ChapterII.Section3.NormalSL2

/-!
# The characteristic power of a Q-group

A finite Q-group with a semidihedral or wreathed Sylow two-subgroup has a
unique source characteristic power. The datum is the odd field order of an
actual characteristic SL2 subgroup in the odd-core quotient, as defined in
`CharacteristicPowerDefs`; no final centralizer model is assumed.

The quotient remains an enlarged Q-group and the quotient map preserves the
chosen Sylow shape. The unique normal SL2 theorem applies there. Uniqueness
under automorphisms makes its normal subgroup characteristic, giving the
required datum. Any other characteristic-power witness is normal as well,
so the same normal-SL2 uniqueness theorem equates the field orders.

This proves the discussion preceding Alperin--Brauer--Gorenstein II.3
Definition 1, article p23 (`page-024.tex`). Both Sylow alternatives and the
field orders three and nine are retained. The QD characteristic power is
assembled separately through involution centralizers.
-/

namespace ABG
open GorensteinWalter
universe u

public theorem exists_unique_sourceQCharacteristicPower
    {G : Type u} [Group G] [Finite G]
    (hQ : IsQGroup G) (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    ∃! q, HasSourceQCharacteristicPower G q := by
  let N := pPrimeCore 2 G
  let R := S.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  obtain ⟨e⟩ := sylow_quotient_equiv S N pPrimeCore_coprime_card
  have hR : Stellmacher.IsSemidihedralGroup R ∨ IsWreathedGroup R := by
    rcases hS with hS | ⟨n, hS⟩
    · exact Or.inl (semidihedral_equiv e hS)
    · exact Or.inr ⟨n, wreathed_equiv e hS⟩
  obtain ⟨F, iF, fF, hF, L, hLN, ⟨eL⟩, hunique⟩ :=
    qGroup_exists_unique_normal_SL2 hQ.oddCore_quotient R hR
      (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
  let : Field F := iF
  let : Finite F := fF
  have hLc : L.Characteristic := by
    apply Subgroup.characteristic_iff_map_eq.mpr
    intro a
    have hnormal : (L.map a.toMonoidHom).Normal := a.normal_map_iff.mpr hLN
    let e' : L.map a.toMonoidHom ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (Subgroup.equivMapOfInjective L a.toMonoidHom a.injective).symm.trans eL
    exact (hunique F iF fF hF _ hnormal ⟨e'⟩).1
  refine ⟨Nat.card F, ⟨F, iF, fF, hF, rfl, L, hLc, ⟨eL⟩⟩, ?_⟩
  intro q hq
  obtain ⟨E, iE, fE, hE, hEq, M, hMc, heM⟩ := hq
  let : Field E := iE
  let : Finite E := fE
  let : M.Characteristic := hMc
  exact hEq.symm.trans (hunique E iE fE hE M inferInstance heM).2

end ABG
