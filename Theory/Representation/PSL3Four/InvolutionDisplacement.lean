module
public import Theory.SpecificGroups.PSL3Four.TernaryNormalizer
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.Representation.AbelianFrobeniusDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Four moved dimensions for every faithful binary PSL₃(4) involution

The explicit Frobenius subgroup E₉:Q₈ has a free orbit of eight character
weights in any faithful representation. Its central involution permutes
those weights in four pairs. Scalar extension and descent give four moved
binary dimensions. Actual involution conjugacy and field transport retain
any given PSL₃(4) marking and the original representation; no irreducibility
or module classification premise is needed.

The Chapter 12 EscapeModulesResidualDisplacement consumer applies this to
the literal residual image and excludes its small-involution four-group.
This supplies a replacement step in Aschbacher--Smith 5.1.23, printed
pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.PSL3Four
open Matrix.PSL3Four.TernaryNormalizer
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem marked_involution_displacement
    (ρ : Representation (ZMod 2) PSL(3,Four) W) (hf : Function.Injective ρ) :
    4 ≤ fixedCodim ρ (zpowers (involution : PSL(3,Four))) := by
  let : Nontrivial nine := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_nine]; decide)
  have hb := prime_displacement_bounds_of_fixedPointFree_normalizer
    ρ nine quaternion hf (by rw [card_nine]; decide) quaternion_normalizes
    quaternion_free involution (by decide : Nat.Prime 2) involution_order
  rw [card_quaternion] at hb
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hb.1

/-- In the actual projective group every involution moves at least four binary dimensions. -/
theorem involution_fixedCodim_ge_four
    (ρ : Representation (ZMod 2) PSL(3,Four) W) (hf : Function.Injective ρ)
    (a : PSL(3,Four)) (ha : orderOf a = 2) : 4 ≤ fixedCodim ρ (zpowers a) := by
  have hc : Nat.card Four = 2 ^ 2 := by rw [Nat.card_eq_fintype_card]; decide
  have ht : orderOf (involution : PSL(3,Four)) = 2 :=
    (orderOf_injective quaternion.subtype quaternion.subtype_injective involution).trans involution_order
  have ha1 : a ≠ 1 := by intro h; simp [h] at ha
  have ht1 : (involution : PSL(3,Four)) ≠ 1 := by intro h; simp [h] at ht
  have ha2 : a ^ 2 = 1 := by
    have he := pow_orderOf_eq_one a
    rwa [ha] at he
  have ht2 : (involution : PSL(3,Four)) ^ 2 = 1 := by
    have he := pow_orderOf_eq_one (involution : PSL(3,Four))
    rwa [ht] at he
  have hconj := (Matrix.PSL3.EvenInnerCentralizers.involution_isConj_root Four
    (by decide) hc (involution : PSL(3,Four)) ht1 ht2).trans
    (Matrix.PSL3.EvenInnerCentralizers.involution_isConj_root Four
      (by decide) hc a ha1 ha2).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  rw [←hg,fixedCodim_zpowers_conj]
  exact marked_involution_displacement ρ hf

/-- Field and group transport retains the supplied representation and involution. -/
theorem involution_fixedCodim_ge_four_of_equiv
    {F X : Type*} [Field F] [Finite F] [Group X]
    (hF : Nat.card F = 4) (e : X ≃* PSL(3,F))
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (a : X) (ha : orderOf a = 2) : 4 ≤ fixedCodim ρ (zpowers a) := by
  let : Fintype F := Fintype.ofFinite F
  let i : Four ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF]
    rw [Nat.card_eq_fintype_card]
    decide)
  let j : PSL(3,Four) ≃* X := (Atlas.fieldEquivPSL 3 i).trans e.symm
  let τ := ρ.comp j.toMonoidHom
  have hb := involution_fixedCodim_ge_four τ (hf.comp j.injective) (j.symm a)
    ((j.symm.orderOf_eq a).trans ha)
  have he := fixedCodim_map_equivariant τ ρ j.toMonoidHom (LinearEquiv.refl _ _)
    (fun _ _ => rfl) (zpowers (j.symm a))
  rw [MonoidHom.map_zpowers] at he
  change fixedCodim τ (zpowers (j.symm a)) = fixedCodim ρ (zpowers (j (j.symm a))) at he
  rw [j.apply_symm_apply] at he
  exact hb.trans_eq he

end Representation.PSL3Four
