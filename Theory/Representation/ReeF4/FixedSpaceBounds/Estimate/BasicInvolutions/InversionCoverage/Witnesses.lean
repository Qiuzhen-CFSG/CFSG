module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.ThirteenCertificate
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.MarkedModel
public import Theory.SpecificGroups.Tits.Atlas1600Parrott

/-!
# Odd-order elements inverted by the marked binary Ree involutions

The Parrott relation gives order five for s₁r₁. A checked permutation
relation gives order thirteen for s₄ times its specified conjugate.
Single moved points exclude the identity. The faithful Parrott comparison
and the marked matrix embedding preserve the orders and inversion identities.
Thus both witnesses lie in the actual derived binary Ree group.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal p.57; Parrott (1972), section 5, p.683, for the presentation.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
open Tits Tits.InvolutionRootGeometry

private theorem atlas_val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem atlas_val_inv (x : Atlas1600Group) : x⁻¹.val = x.val⁻¹ := rfl
private theorem atlas_val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl
private theorem atlas_val_one : (1 : Atlas1600Group).val = 1 := rfl

private theorem parrott_thirteen_pow : thirteenWord parrottGenerator ^ 13 = 1 := by
  apply parrottFiniteImageEquiv.injective
  apply Subtype.ext
  simpa only [thirteenWord, thirteenConjugator, map_mul, map_inv, map_pow, map_one,
    parrottFiniteImageEquiv_generator, atlas_val_mul, atlas_val_inv,
    atlas_val_pow, atlas_val_one, atlas1600ParrottAssignment_val]
    using atlas_thirteen_pow

private theorem parrott_thirteen_ne_one : thirteenWord parrottGenerator ≠ 1 := by
  intro h
  have he := congrArg (fun x : ParrottGroup =>
    (parrottFiniteImageEquiv x).val (0 : Fin 1600)) h
  simp only [thirteenWord, thirteenConjugator, map_mul, map_inv, map_one,
    parrottFiniteImageEquiv_generator, atlas_val_mul, atlas_val_inv, atlas_val_one,
    atlas1600ParrottAssignment_val] at he
  have hn : thirteenWord Atlas1600ParrottData.permutation (0 : Fin 1600) ≠ 0 := by
    decide +kernel
  exact hn he

private theorem parrott_five_ne_one :
    parrottGenerator .s1 * parrottGenerator .r1 ≠ 1 := by
  intro h
  have he := congrArg (fun x : ParrottGroup =>
    (parrottFiniteImageEquiv x).val (0 : Fin 1600)) h
  simp only [map_mul, map_one, parrottFiniteImageEquiv_generator, atlas_val_mul,
    atlas_val_one, atlas1600ParrottAssignment_val] at he
  have hn : (Atlas1600ParrottData.permutation .s1 *
      Atlas1600ParrottData.permutation .r1) (0 : Fin 1600) ≠ 0 := by decide +kernel
  exact hn he

private theorem parrott_five_order :
    orderOf (parrottGenerator .s1 * parrottGenerator .r1) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime _ parrott_five_ne_one
  simpa only [parrottRelator, map_mul, map_pow, FreeGroup.lift_apply_of] using
    parrott_generators_satisfy_relations .vi_s1_r1

private theorem parrott_thirteen_order : orderOf (thirteenWord parrottGenerator) = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact orderOf_eq_prime parrott_thirteen_pow parrott_thirteen_ne_one

private theorem involution_inverts_product {G : Type*} [Group G]
    (s r : G) (hs : s ^ 2 = 1) (hr : r ^ 2 = 1) :
    s * (s * r) * s⁻¹ = (s * r)⁻¹ := by
  have hs' : s * s = 1 := by simpa only [pow_two] using hs
  have hr' : r * r = 1 := by simpa only [pow_two] using hr
  have hi : r⁻¹ = r := by
    have h := congrArg (fun x => r⁻¹ * x) hr'
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using h.symm
  simp only [mul_inv_rev, hi, ← mul_assoc, hs', one_mul]

noncomputable def binaryFive : Model 0 := embedding (parrottGenerator .s1 * parrottGenerator .r1)
noncomputable def binaryThirteen : Model 0 := embedding (thirteenWord parrottGenerator)

theorem binaryFive_order : orderOf binaryFive = 5 :=
  (orderOf_injective embedding embedding_injective _).trans parrott_five_order

theorem binaryThirteen_order : orderOf binaryThirteen = 13 :=
  (orderOf_injective embedding embedding_injective _).trans parrott_thirteen_order

theorem binaryFive_inverted :
    fixedGenerator .s1 * binaryFive * (fixedGenerator .s1)⁻¹ = binaryFive⁻¹ := by
  have hs : parrottGenerator .s1 ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .i_s1
  have hr : parrottGenerator .r1 ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .i_r1
  simpa only [binaryFive, map_mul, map_inv, embedding_generator] using
    congrArg embedding (involution_inverts_product _ _ hs hr)

theorem binaryThirteen_inverted :
    fixedGenerator .s4 * binaryThirteen * (fixedGenerator .s4)⁻¹ = binaryThirteen⁻¹ := by
  have hs : parrottGenerator .s4 ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .i_s4
  have hr := congrArg (MulAut.conj (thirteenConjugator parrottGenerator)) hs
  have h := involution_inverts_product (parrottGenerator .s4)
    (MulAut.conj (thirteenConjugator parrottGenerator) (parrottGenerator .s4)) hs
    (by simpa only [map_pow, map_one] using hr)
  simpa only [binaryThirteen, thirteenWord, MulAut.conj_apply, map_mul, map_inv,
    embedding_generator] using congrArg embedding h

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
