module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.NormalSubgroups
public import Theory.Representation.BinaryOffender.GeneratedCore
/-!
# The prime-product obstruction on the actual terminal offender actor

Normality and the nontrivial source commutator put the PSL₂(p) factor in
the Thompson image, hence in the offender subgroup of the original quotient
action. Thus the defining prime p ≥ 11 divides that actor's order. Its
inclusion in the ambient quotient also shows that sixteen does not divide
its order. Restricting the original action supplies offender generation.

The final theorem consumes a prime-divisor bound on this same actor. The
remaining independent comparison must derive that bound from the complete
B.5.6 alternatives and the proved Sylow bound. No FF classification or actor
equality is asserted here. These deductions apply to both local labelings.

Source: Aschbacher–Smith, F.6.18(3), printed p.309, B.5.1/B.5.6,
printed pp.99–105, and the terminal intersection on printed p.1155.
-/

public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)

private theorem primeProduct_sylow_card
    (hS : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) : Nat.card d.quotientSylow = 8 := by
  obtain ⟨e⟩ := hS
  rw [Nat.card_congr e.toEquiv]
  exact DihedralGroup.nat_card

/-- The actual component lies in the original Thompson image. -/
theorem primeProduct_first_le_thompson (c : FSource.ProductRow d.quotientSylow)
    (hS : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) :
    c.first ≤ (thompsonGroup H).map coreProjection :=
  LowRows.PrimeProduct.first_le_of_normal_nonabelian c (d.primeProduct_sylow_card hS)
    _ d.thompson_image_commutator_ne_bot

variable [IsElementaryAbelian 2 (moduleClosure V)]

/-- The same component lies in the actual offender subgroup. -/
theorem primeProduct_first_le_offender (c : FSource.ProductRow d.quotientSylow)
    (hS : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) : c.first ≤ d.offenderGroup :=
  (d.primeProduct_first_le_thompson c hS).trans d.thompson_image_le_offender

/-- Its defining prime divides the order of the original offender actor. -/
theorem primeProduct_prime_dvd_offender (c : FSource.ProductRow d.quotientSylow)
    (hS : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) :
    c.field.prime ∣ Nat.card d.offenderGroup :=
  (LowRows.PrimeProduct.prime_dvd_first_card c).trans
    (card_dvd_of_injective (Subgroup.inclusion (d.primeProduct_first_le_offender c hS))
      (Subgroup.inclusion_injective _))

/-- The literal ambient Sylow bounds the two-part of the offender actor. -/
theorem primeProduct_no_sixteen_dvd_offender
    (hS : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) :
    ¬ 16 ∣ Nat.card d.offenderGroup := by
  intro h
  have hd : 2 ^ 4 ∣ Nat.card (coreQuotient H) :=
    h.trans (card_dvd_of_injective d.offenderGroup.subtype d.offenderGroup.subtype_injective)
  have hs := d.quotientSylow.pow_dvd_card_of_pow_dvd_card hd
  rw [d.primeProduct_sylow_card hS] at hs
  norm_num at hs

omit [Finite H] in
/-- The restricted original representation satisfies B.5.3 generation. -/
theorem primeProduct_offender_generated : offenderSubgroup d.offenderAction = ⊤ :=
  offenderSubgroup_restrict_eq_top _

/-- The remaining FF model comparison, once proved on this actor, excludes
the product row without choosing a local labeling. This is a conditional
reduction, not yet the full F.6.18/B.5.6 comparison. -/
theorem no_primeProduct_row_of_offender_prime_bound
    (c : FSource.ProductRow d.quotientSylow)
    (hS : Nonempty (d.quotientSylow ≃* DihedralGroup 4))
    (bound : ∀ p : ℕ, p.Prime → p ∣ Nat.card d.offenderGroup → p ≤ 7) : False := by
  have hlarge := LowRows.PrimeProduct.prime_lower c
  have hsmall := bound c.field.prime c.field.prime_isPrime
    (d.primeProduct_prime_dvd_offender c hS)
  omega

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
