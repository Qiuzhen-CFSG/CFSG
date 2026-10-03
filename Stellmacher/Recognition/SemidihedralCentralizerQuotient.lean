module
public import ABG.ChapterII.Section2.SemidihedralCentralizerSylow
public import ABG.ChapterII.Section3.CharacteristicPowerQuotient
public import ABG.ChapterII.Section3.SourceThreeSemidihedralModel
public import Stellmacher.Recognition.SourceCharacteristicThree
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!+# Involution centralizers modulo their odd cores in the semidihedral N2 branch

For a finite simple N2 group with a supplied semidihedral Sylow subgroup,
every involution centralizer modulo its odd core is GL2(3). In particular,
the supplied Sylow subgroup has order sixteen, without any assumption on
the local odd cores.

QD fusion places a conjugate of the supplied Sylow in each centralizer.
Quotienting by the odd core preserves this Sylow and the source
characteristic-three datum. The core-free Q-group model then identifies
the quotient. Its order forty-eight gives the Sylow order.

Source: ABG II.2 Proposition 1, II.3 Lemma 1 and Proposition 3, and the
local calculations preceding III.8 Proposition 1 (article p111).
Eliminating the odd core itself is a separate global argument.
-/

namespace Stellmacher.Recognition
open ABG
universe u

/-- The actual odd-core quotient of each involution centralizer is GL2(3). -/
public theorem involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    Nonempty ((Subgroup.centralizer ({x} : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) ≃* GL2 3 1) := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  obtain ⟨T, hT, _⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  let C := Subgroup.centralizer ({x} : Set G)
  let O := pPrimeCore 2 C
  let R := T.mapSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  obtain ⟨e⟩ := sylow_quotient_equiv T O pPrimeCore_coprime_card
  have hR : HasQuasiDihedralSylowTwoSubgroups (C ⧸ O) :=
    ⟨R, semidihedral_equiv e hT⟩
  have hq := (sourceCharacteristicPower_three_of_simple_nTwo ⟨S, hS⟩ hN).at_involution
    hQD x hx
  exact qGroup_equiv_gl2_three_of_corefree_semidihedral
    (qd_involutionCentralizer_isQGroup hQD x hx).1.oddCore_quotient
    (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2)) hR hq.oddCore_quotient

private theorem gl2_three_card : Nat.card (GL2 3 1) = 48 := by
  let : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide)]
  norm_num

/-- The centralizer order is forty-eight times its odd-core order. -/
public theorem involutionCentralizer_card_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      48 * Nat.card (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  have hc := Nat.card_congr e.toEquiv
  rw [gl2_three_card] at hc
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))), hc]

/-- The supplied semidihedral Sylow has order sixteen before eliminating local odd cores. -/
public theorem semidihedral_sylow_card_sixteen_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G) :
    Nat.card S = 16 := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  obtain ⟨x, hx, _⟩ := sourceCharacteristicPower_three_of_simple_nTwo ⟨S, hS⟩ hN
  obtain ⟨T, _, ⟨eT⟩⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  let C := Subgroup.centralizer ({x} : Set G)
  let O := pPrimeCore 2 C
  let R := T.mapSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  obtain ⟨eR⟩ := sylow_quotient_equiv T O pPrimeCore_coprime_card
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  have hc : Nat.card (C ⧸ O) = 48 := (Nat.card_congr e.toEquiv).trans gl2_three_card
  have hR : Nat.card R = 16 := by
    rw [R.card_eq_multiplicity, hc]
    rw [show 48 = 2 ^ 4 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization]
    norm_num
  exact (Nat.card_congr (eT.trans eR).toEquiv).trans hR

end Stellmacher.Recognition
