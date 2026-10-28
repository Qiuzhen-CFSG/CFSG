module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality

/-!
# The two-part of max4 from its normal closure and quotient image

Let Q be the relative normal closure of `(x*y²)^6` in the literal ATLAS
max4 subgroup. If Q is a two-group, every epimorphism to S₅ × SL₃(2)
kills Q, since that actual target has trivial two-core. A cardinality
lower bound `2^15 ≤ |Q|` therefore supplies `2^15` in the kernel order.
Kernel-image counting supplies the remaining factor `20160`, whose
two-part is `2^6`.

The final theorem `max4_twoPart_dvd` discharges these inputs with the
actual product action, the certified block-unipotent normal closure, and
the injective binary products of fifteen literal words. The eleven initial
coordinate identities needed by the counting certificate are supplied by
`CharacteristicTwo.NormalClosure`. The conditional assembly APIs remain
available separately.

Source context: Kleidman--Wilson (1988), pp.484--510; Aschbacher--Smith,
Proposition 1.3.4, printed p.511/PDF p.528 of `refs/quasithin.pdf`.
The actual word bytes and their provenance are retained beside
`SymmetricLinear.Model`. Q uses intrinsic normality in that exact carrier.
-/

public section

namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup

/-- A normal two-subgroup is killed by the actual max4 quotient epimorphism. -/
theorem seedNormalClosure_le_ker_of_surjective
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    (hQ : IsPGroup 2 CharacteristicTwo.seedNormalClosure) :
    CharacteristicTwo.seedNormalClosure ≤ f.ker := by
  have hn : (CharacteristicTwo.seedNormalClosure.map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hm : CharacteristicTwo.seedNormalClosure.map f ≤ pCore 2 QuotientModel :=
    le_sSup ⟨hn, hQ.map f⟩
  rw [quotientModel_twoCore] at hm
  exact Subgroup.map_le_iff_le_comap.mp hm

/-- The seed lower bound and actual epimorphism give the full expected local
order as a divisor, without an upper bound or an abstract recognition claim. -/
theorem max4_localOrder_dvd_of_seed_card
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    (hQ : IsPGroup 2 CharacteristicTwo.seedNormalClosure)
    (hc : 2 ^ 15 ≤ Nat.card CharacteristicTwo.seedNormalClosure) :
    2 ^ 15 * 20160 ∣ Nat.card max4Subgroup := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hexp : 15 ≤ n := by
    rw [hn] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hd : 2 ^ 15 ∣ Nat.card f.ker :=
    (hn ▸ (pow_dvd_pow 2 hexp)).trans
      (card_dvd_of_le (seedNormalClosure_le_ker_of_surjective f hf hQ))
  have hcount := f.ker.card_mul_index
  rw [index_ker, f.range_eq_top_of_surjective hf, card_top, quotientModel_card] at hcount
  rw [← hcount]
  exact Nat.mul_dvd_mul hd (dvd_refl _)

/-- The precise input required by the intrinsic Sylow comparison, assembled
from the three independent concrete max4 certificates. -/
theorem max4_twoPart_dvd_of_seed_card
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    (hQ : IsPGroup 2 CharacteristicTwo.seedNormalClosure)
    (hc : 2 ^ 15 ≤ Nat.card CharacteristicTwo.seedNormalClosure) :
    2 ^ 21 ∣ Nat.card max4Subgroup := by
  have hdiv : 2 ^ 21 ∣ 2 ^ 15 * 20160 := by decide
  exact hdiv.trans (max4_localOrder_dvd_of_seed_card f hf hQ hc)

/-- The fifteen actual words reduce the remaining kernel count to their
binary-product injectivity certificate. -/
theorem max4_twoPart_dvd_of_binaryProduct_injective
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    (hQ : IsPGroup 2 CharacteristicTwo.seedNormalClosure)
    (h : Function.Injective SylowTwoPart.binaryProduct) :
    2 ^ 21 ∣ Nat.card max4Subgroup :=
  max4_twoPart_dvd_of_seed_card f hf hQ
    (SylowTwoPart.seed_card_lower_of_binaryProduct_injective h)

/-- The literal ATLAS max4 subgroup contains the full ambient two-part.
All coordinate, normal-closure and quotient-image premises are discharged. -/
theorem max4_twoPart_dvd : 2 ^ 21 ∣ Nat.card max4Subgroup :=
  max4_twoPart_dvd_of_binaryProduct_injective
    max4Projection max4Projection_surjective CharacteristicTwo.seedNormalClosure_isPGroup
    (SylowTwoPart.binaryProduct_injective_of_coordinates
      CharacteristicTwo.seedConjugate_coordinates)

end Janko4.LocalStructure.SymmetricLinear
