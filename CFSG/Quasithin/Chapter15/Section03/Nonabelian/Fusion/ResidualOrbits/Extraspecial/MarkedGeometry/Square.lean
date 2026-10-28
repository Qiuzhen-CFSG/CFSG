module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Coordinates

/-!
# Identifying the extraspecial square form

The power-map orthogonal space of 15.3.56(1) can be expressed in any additive
coordinates on the literal U/Z. Its form is initially unspecified. The genuine
total singularity of the summands in the proof of 15.3.58 is imposed on their
actual subgroup preimages. Squaring and the fact that H centralizes z imply
invariance. Uniqueness of the natural/dual invariant form then identifies this
power map with evaluation, including the mixed square formula.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(1), 15.3.58 and its proof, printed pp.1147–1149.
-/

@[expose] public section
open Subgroup BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial

variable {G : Type*} [Group G] {T Z ZS V : Subgroup G} {t z : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The earlier power-map form of 15.3.56(1), transported along the additive
coordinates of 15.3.58. No evaluation formula or involution orbit is assumed.
The central coordinate is the actual marked generator z. -/
structure SquareForm (d : RecognizedAction T Z ZS V t) (z : G) where
  form : QuadraticForm (ZMod 2) NaturalDualSpace
  nondegenerate : form.polarBilin.Nondegenerate
  square : ∀ x : closureU Z ZS, (x : G) ^ 2 =
    z ^ (form (d.coordinates (QuotientGroup.mk' _ x)).toAdd).val

private theorem binary_power_injective (hz : orderOf z = 2) :
    Function.Injective (fun a : ZMod 2 => z ^ a.val) := by
  intro a b he
  apply ZMod.val_injective
  apply pow_injOn_Iio_orderOf (x := z) _ _ he
  · simpa only [Set.mem_Iio, hz] using a.val_lt
  · simpa only [Set.mem_Iio, hz] using b.val_lt

private theorem binary_power_eq_one (hz : orderOf z = 2) (a : ZMod 2) :
    z ^ a.val = 1 ↔ a = 0 := by
  constructor
  · intro h
    exact binary_power_injective hz (h.trans (pow_zero z).symm)
  · rintro rfl
    exact pow_zero z

variable (d : RecognizedAction T Z ZS V t) (s : SquareForm d z)

private theorem squareForm_invariant (hz : orderOf z = 2) (hzZ : z ∈ Z)
    (h : centralizerH Z) (w : VectorQuotient Z ZS) :
    s.form (d.coordinates (quotientAction Z ZS h w)).toAdd =
      s.form (d.coordinates w).toAdd := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w
  rw [quotientAction_mk]
  apply binary_power_injective hz
  dsimp only
  rw [← s.square, ← s.square]
  change ((h : G) * (x : G) * (h : G)⁻¹) ^ 2 = (x : G) ^ 2
  rw [← MulAut.conj_apply, ← map_pow, s.square, map_pow]
  have hc : MulAut.conj (h : G) z = z := by
    change (h : G) * z * (h : G)⁻¹ = z
    rw [← mem_centralizer_iff.mp h.property z hzZ, mul_inv_cancel_right]
  rw [hc]

/-- The actual square form is evaluation. Only the natural preimage needs
an explicit total-singularity input: t transports it to the dual preimage. -/
theorem squareForm_eq_quadratic (hz : orderOf z = 2) (hzZ : z ∈ Z)
    (hnatural : ∀ x ∈ naturalPreimage d, x ^ 2 = 1) : s.form = quadratic := by
  have h₁ : ∀ w : BinaryLinearThree.Vector, s.form (w, 0) = 0 := by
    intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS))
      (d.coordinates.symm (Multiplicative.ofAdd (w, 0)))
    have he : (d.coordinates (QuotientGroup.mk' _ x)).toAdd = (w, 0) := by
      rw [hx, d.coordinates.apply_symm_apply]
      rfl
    have hm : (x : G) ∈ naturalPreimage d := (mem_naturalPreimage d x).mpr
      (congrArg Prod.snd he)
    apply (binary_power_eq_one hz _).mp
    rw [← he, ← s.square]
    exact hnatural x hm
  apply quadratic_unique s.form h₁
  · intro f
    let w := d.coordinates.symm (Multiplicative.ofAdd (0, f))
    have he := squareForm_invariant d s hz hzZ ⟨t, d.t_mem_H⟩ w
    have hd := d.swaps_dual f
    have hn : s.form (d.coordinates (quotientAction Z ZS ⟨t, d.t_mem_H⟩ w)).toAdd = 0 := by
      rw [show (d.coordinates (quotientAction Z ZS ⟨t, d.t_mem_H⟩ w)).toAdd =
        ((d.coordinates (quotientAction Z ZS ⟨t, d.t_mem_H⟩ w)).toAdd.1, 0) from Prod.ext rfl hd]
      exact h₁ _
    simpa only [w, d.coordinates.apply_symm_apply, toAdd_ofAdd] using he.symm.trans hn
  · intro g w
    obtain ⟨h, hh⟩ := exists_quotient_action_linear d g
    have he := squareForm_invariant d s hz hzZ h
      (d.coordinates.symm (Multiplicative.ofAdd w))
    simpa only [hh, d.coordinates.apply_symm_apply, toAdd_ofAdd] using he
  · exact s.nondegenerate

include s

/-- The mixed square formula on every actual lift in U. -/
theorem square_eq_evaluation (hz : orderOf z = 2) (hzZ : z ∈ Z)
    (hnatural : ∀ x ∈ naturalPreimage d, x ^ 2 = 1) (x : closureU Z ZS) :
    (x : G) ^ 2 = z ^
      ((d.coordinates (QuotientGroup.mk' _ x)).toAdd.2
        (d.coordinates (QuotientGroup.mk' _ x)).toAdd.1).val := by
  rw [s.square, squareForm_eq_quadratic d s hz hzZ hnatural]
  rfl

/-- Involutory lifts are exactly the zero locus of the evaluation form. -/
theorem square_eq_one_iff_quadratic_zero (hz : orderOf z = 2) (hzZ : z ∈ Z)
    (hnatural : ∀ x ∈ naturalPreimage d, x ^ 2 = 1) (x : closureU Z ZS) :
    (x : G) ^ 2 = 1 ↔ quadratic (d.coordinates (QuotientGroup.mk' _ x)).toAdd = 0 := by
  rw [s.square, squareForm_eq_quadratic d s hz hzZ hnatural]
  exact binary_power_eq_one hz _

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
