module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.SmallerResidual
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.FieldTheory.OddQuadraticCoefficientLift

/-!
# Even field involutions of genuine binary triality groups

For an actual inner-times-coefficient expression of a non-inner involution,
its image in the outer group has order two and lies in the image of the
cyclic coefficient group of order 3n. Thus n = 2m for some positive m,
without any global automorphism-coverage or faithfulness assumption.

The original conditional assembly combines normalization of the inner factor,
identification of the canonical coefficient fixed group, and the smaller
carrier's two-residual identity. The final specialization discharges that
residual identity using the proved perfectness of the genuine smaller carrier.
Normalization and fixed-group descent remain explicit model inputs. The
transport uses compatible multiplicative isomorphisms of the literal fixed
subgroups and their own p-residuals, retaining the derived subgroup at m = 1.

The scalar and split-group inputs are proved in `EvenFieldFixedResidual.Twist`.
The remaining descent must pass through the elementary subgroup and its own
central quotient, and compare the inverse diagram cycle with the canonical
smaller triality construction. Equality of field or group orders cannot
replace this comparison.

Sources: Aschbacher–Smith, Notation 16.1.3 and 16.1.4(4), printed p.1171,
`refs/quasithin.pdf`; GLS3 §§2.5–2.6, especially 2.5.12(d), 2.5.13(c),
and 2.5.17, `refs/KGroup/GLS3/chapter2.tex`. The outer involutions are field
automorphisms in the GLS convention.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField
open OuterOdd

/-- The explicit inner-coefficient expression already forces the base exponent
of a non-inner involution to be even, without faithfulness or coverage. -/
theorem even_parameter_of_noninner_inner_coefficient
    (n : ℕ) (hn : 0 < n) (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e) :
    ∃ (m : ℕ), 0 < m ∧ n = 2*m := by
  let P := binaryParameters n hn
  let q : MulAut (BinaryCarrier n hn) →* MulAut.Outer (BinaryCarrier n hn) :=
    QuotientGroup.mk' _
  have hqne : q a ≠ 1 := fun h => houter ((QuotientGroup.eq_one_iff a).mp h)
  have hq2 : q a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hqo : orderOf (q a) = 2 := orderOf_eq_prime hq2 hqne
  have hqe : q a = outerCoefficientAction P e := by
    have hqg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rw [hform, map_mul, hqg, one_mul]
    rfl
  have hc : Nat.card (CoefficientAut P) = 3*n := by
    exact GaloisField.card_ringAut 2 (3*n) (by omega)
  have hd := (orderOf_map_dvd (outerCoefficientAction P) e).trans (orderOf_dvd_natCard e)
  rw [← hqe, hqo, hc] at hd
  have hn2 : 2 ∣ n := (Nat.Prime.dvd_mul Nat.prime_two).mp hd |>.resolve_left (by decide)
  obtain ⟨m, hm⟩ := hn2
  exact ⟨m, by omega, hm⟩

private def residualEquivDerived {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : pResidual 2 H = commutator H) : pResidual 2 G ≃* commutator H :=
  ((pResidual 2 G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr ((Subgroup.map_pResidual 2 e).trans h))

private theorem conjugate_eq_of_compatible {G : Type*} [Group G]
    (a b c : MulAut G) (h : ∀ x, b (a x) = c (b x)) : b*a*b⁻¹ = c := by
  apply MulEquiv.ext
  intro x
  change b (a (b.symm x)) = c x
  simpa only [b.apply_symm_apply] using h (b.symm x)

private theorem orderOf_eq_of_compatible {G : Type*} [Group G]
    (a b c : MulAut G) (h : ∀ x, b (a x) = c (b x)) : orderOf c = orderOf a := by
  have hc : MulAut.conj b a = c := conjugate_eq_of_compatible a b c h
  rw [← hc]
  exact (MulAut.conj b).orderOf_eq a

/-- Conditional assembly from normalization of the inner factor, descent of
the canonical field fixed group, and the smaller carrier's residual identity.
This retained conditional interface keeps all three model inputs explicit. -/
theorem fixed_model_and_residual_of_normalization_descent
    (n : ℕ) (hn : 0 < n) (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (hnormalize : ∀ (m : ℕ), 0 < m → n = 2*m →
      ∃ b : MulAut (BinaryCarrier n hn), ∀ x, b (a x) =
        coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) (b x))
    (hdescent : ∀ (m : ℕ) (hm : 0 < m), n = 2*m →
      Nonempty ((coefficientAction (binaryParameters n hn)
        (coefficientFrobenius n hn (3*m))).fixedSubgroup ≃* BinaryCarrier m hm))
    (hresidual : ∀ (m : ℕ) (hm : 0 < m),
      pResidual 2 (BinaryCarrier m hm) = commutator (BinaryCarrier m hm)) :
    ∃ (m : ℕ) (hm : 0 < m), n = 2*m ∧
      orderOf (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) = 2 ∧
      (∃ b : MulAut (BinaryCarrier n hn),
        b*a*b⁻¹ = coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) ∧
      Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (BinaryCarrier m hm)) := by
  obtain ⟨m, hm, hnm⟩ := even_parameter_of_noninner_inner_coefficient n hn a ha houter g e hform
  obtain ⟨b, hb⟩ := hnormalize m hm hnm
  obtain ⟨d⟩ := hdescent m hm hnm
  have haorder : orderOf a = 2 := orderOf_eq_prime ha
    (fun h => houter (h ▸ (MulAut.innerSubgroup (BinaryCarrier n hn)).one_mem))
  let c := MulAut.fixedSubgroupEquivOfCompatible b a
    (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) hb
  exact ⟨m, hm, hnm, (orderOf_eq_of_compatible a b _ hb).trans haorder,
    ⟨b, conjugate_eq_of_compatible a b _ hb⟩, ⟨c.trans d⟩,
    ⟨residualEquivDerived (c.trans d) (hresidual m hm)⟩⟩

/-- Field-fixed assembly with the smaller two-residual premise discharged by
actual binary triality perfectness. Only the independent normalization and
fixed-group descent inputs remain, and the smaller exponent may be one. -/
theorem fixed_model_and_residual_of_normalization_and_descent
    (n : ℕ) (hn : 0 < n) (a : MulAut (BinaryCarrier n hn))
    (ha : a^2 = 1) (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (hnormalize : ∀ (m : ℕ), 0 < m → n = 2*m →
      ∃ b : MulAut (BinaryCarrier n hn), ∀ x, b (a x) =
        coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) (b x))
    (hdescent : ∀ (m : ℕ) (hm : 0 < m), n = 2*m →
      Nonempty ((coefficientAction (binaryParameters n hn)
        (coefficientFrobenius n hn (3*m))).fixedSubgroup ≃* BinaryCarrier m hm)) :
    ∃ (m : ℕ) (hm : 0 < m), n = 2*m ∧
      orderOf (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) = 2 ∧
      (∃ b : MulAut (BinaryCarrier n hn),
        b*a*b⁻¹ = coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) ∧
      Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (BinaryCarrier m hm)) := by
  obtain ⟨m, hm, hnm⟩ := even_parameter_of_noninner_inner_coefficient n hn a ha houter g e hform
  obtain ⟨b, hb⟩ := hnormalize m hm hnm
  obtain ⟨d⟩ := hdescent m hm hnm
  have haorder : orderOf a = 2 := orderOf_eq_prime ha
    (fun h => houter (h ▸ (MulAut.innerSubgroup (BinaryCarrier n hn)).one_mem))
  let c := MulAut.fixedSubgroupEquivOfCompatible b a
    (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) hb
  exact ⟨m, hm, hnm, (orderOf_eq_of_compatible a b _ hb).trans haorder,
    ⟨b, conjugate_eq_of_compatible a b _ hb⟩, ⟨c.trans d⟩,
    ⟨fixedResidualEquivSmallerDerived a m hm (c.trans d)⟩⟩

end Triality.Standard.EvenField
