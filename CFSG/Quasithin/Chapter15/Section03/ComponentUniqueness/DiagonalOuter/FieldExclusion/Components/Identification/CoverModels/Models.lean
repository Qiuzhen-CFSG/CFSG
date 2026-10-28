module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.CoverModels.Reduction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Selecting the two special-linear covers by their actual orders

The central quotients PSL₃(4), J₂ and PSL₃(7) have orders 20160, 604800
and 1876896. A center of order three multiplies these by three. The
special-linear order formula forces field order four or seven, and the
finite-field equivalence gives the actual required matrix-group isomorphism.

For a unitary cover, the kernel of the natural map to the projective image
lies in the center, so its order is one or three. Huppert's projective
unitary order formula is incompatible with all three cover orders. This
uses the stored field involution and an actual Hermitian basis change;
the matrix field has order q² and its fixed field has order q. The
alternating and Mathieu three-covers are excluded by their quotient orders.

The finite arithmetic checks first bound q < 16. They require no order or
simplicity certification for any other catalogue entry.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, A.3.6(2),
printed pp.43--45, and proof of 15.3.38, p.1137; Huppert II.10.12.
Model formulas and the ATLAS J₂ order are reused from the attributed imports.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.CoverModels

private theorem linear_order_parameters {q : ℕ} (hq : 2 ≤ q)
    (h : q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) = 60480 ∨
      q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) = 1814400 ∨
      q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) = 5630688) : q = 4 ∨ q = 7 := by
  have hbound : q < 16 := by
    by_contra hq16
    have hq16 : 16 ≤ q := by omega
    have h2 : 256 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq16 2
    have h3 : 4096 ≤ q ^ 3 := by simpa using Nat.pow_le_pow_left hq16 3
    have hb : 4096 * 4095 * 255 ≤ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega)) (by omega)
    omega
  interval_cases q <;> norm_num at h <;> omega

private theorem unitary_order_impossible {q k : ℕ} (hq : 2 ≤ q) (hk : k = 1 ∨ k = 3)
    (h : ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)) * k = 60480 ∨
      ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)) * k = 1814400 ∨
      ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)) * k = 5630688) : False := by
  have hbound : q < 16 := by
    by_contra hq16
    have hq16 : 16 ≤ q := by omega
    have h2 : 256 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq16 2
    have h3 : 4096 ≤ q ^ 3 := by simpa using Nat.pow_le_pow_left hq16 3
    have hb : 4097 * 4096 * 255 ≤ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) h3) (by omega)
    have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hl : 1 ≤ k := by omega
    have hc : (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ≤ 5630688 := by
      have := Nat.le_mul_of_pos_right
        ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)) hl
      omega
    have hdiv := Nat.mod_add_div ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1)) (Nat.gcd 3 (q + 1))
    have hmod := Nat.mod_lt ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1))
      (Nat.gcd_pos_of_pos_left (q + 1) (by decide : 0 < 3))
    have hmul := Nat.mul_le_mul hg hc
    omega
  interval_cases q <;> rcases hk with rfl | rfl <;> norm_num at h


private theorem card_sl_three {F : Type*} [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F

private noncomputable def sl_three_equiv_of_card_eq {F E : Type*}
    [Field F] [Finite F] [Field E] [Finite E] (hc : Nat.card F = Nat.card E) :
    SL(3,F) ≃* SL(3,E) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  have h : Fintype.card F = Fintype.card E := by
    simpa only [← Nat.card_eq_fintype_card] using hc
  let e : F ≃+* E := FiniteField.ringEquivOfCardEq h
  exact Atlas.fieldEquivSL 3 e

private theorem select_linear {X : Type*} [Group X] [Finite X] {q : ℕ}
    (hi : IsSL X 3 q)
    (hc : Nat.card X = 60480 ∨ Nat.card X = 1814400 ∨ Nat.card X = 5630688) :
    Nonempty (X ≃* Matrix.PSL3Four.SL) ∨ Nonempty (X ≃* SL(3,ZMod 7)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hi
  have hX : Nat.card X = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_sl_three, hcard]
  have hq : 2 ≤ q := by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hparam := linear_order_parameters hq (hX ▸ hc)
  have transfer (E : Type) [Field E] [Finite E] (hE : Nat.card E = q) :
      Nonempty (X ≃* SL(3,E)) :=
    ⟨e.trans (sl_three_equiv_of_card_eq (hcard.trans hE.symm))⟩
  rcases hparam with hfour | hseven
  · exact Or.inl (transfer Matrix.PSL3Four.F (Matrix.PSL3Four.card_F.trans hfour.symm))
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact Or.inr (transfer (ZMod 7) ((Nat.card_zmod 7).trans hseven.symm))

private theorem unitary_projective_card {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {q : ℕ}
    (hq : CoverParameter true q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hfixed : Nat.card {x : F // J.conj x = x} = q := by
    rcases hq with ⟨n, hn, rfl, _⟩ | ⟨hp, _⟩
    · exact FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega)
        hcard hconj
    · let : Fact q.Prime := ⟨hp⟩
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj q 1 (by decide) (by simpa using hcard) (by simpa using hconj)
  obtain ⟨e⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J q hcard hfixed
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, _, _, horder, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12
      (BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
      q hcard hfixed rfl
  exact horder

private theorem exclude_unitary {X : Type*} [Group X] [Finite X] {q : ℕ}
    (hq : CoverParameter true q) (hi : IsSU X 3 q)
    (hz : Nat.card (center X) = 3)
    (hc : Nat.card X = 60480 ∨ Nat.card X = 1814400 ∨ Nat.card X = 5630688) : False := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hi
  have hZ : Nat.card (center J.specialSubgroup) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).symm.trans hz
  have hk : Nat.card J.specialToProjective.ker = 1 ∨
      Nat.card J.specialToProjective.ker = 3 := by
    apply (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
    have hd := card_dvd_of_le J.specialToProjective_ker_le_center
    rwa [hZ] at hd
  have hX : Nat.card X =
      ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)) *
        Nat.card J.specialToProjective.ker := by
    rw [Nat.card_congr e.toEquiv, card_eq_card_quotient_mul_card_subgroup J.specialToProjective.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
        J.specialToProjective_surjective).toEquiv,
      unitary_projective_card J hq hcard hconj]
  have hq2 : 2 ≤ q := by
    have : 1 < Nat.card F := Finite.one_lt_card
    by_contra h
    have hq1 : q ≤ 1 := by omega
    have hh : q ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left hq1 2
    omega
  exact unitary_order_impossible hq2 hk (hX ▸ hc)

/-- The full A.3.6 list at the three possible cover orders consists precisely
of the two required special-linear carriers. No cover-recognition premise is used. -/
theorem select_threeCover {X : Type*} [Group X] [Finite X]
    (hmodel : ThreeCoverModel X) (hz : Nat.card (center X) = 3)
    (hc : Nat.card X = 60480 ∨ Nat.card X = 1814400 ∨ Nat.card X = 5630688) :
    Nonempty (X ≃* Matrix.PSL3Four.SL) ∨ Nonempty (X ≃* SL(3,ZMod 7)) := by
  have hquot := card_eq_card_quotient_mul_card_subgroup (center X)
  rw [hz] at hquot
  cases hmodel with
  | classical b q hq hi =>
      cases b
      · exact select_linear hi hc
      · exact (exclude_unitary hq hi hz hc).elim
  | alternating_six hi =>
      obtain ⟨e⟩ := hi.2.2
      rw [Nat.card_congr e.toEquiv] at hquot
      rw [nat_card_alternatingGroup, Nat.card_fin] at hquot
      norm_num at hquot
      omega
  | alternating_seven hi =>
      obtain ⟨e⟩ := hi.2.2
      rw [Nat.card_congr e.toEquiv] at hquot
      rw [nat_card_alternatingGroup, Nat.card_fin] at hquot
      norm_num at hquot
      omega
  | mathieu hi =>
      obtain ⟨e⟩ := hi.2.2
      rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m22_order] at hquot
      omega

/-- The exact simple central-quotient alternatives give these three orders. -/
theorem field_quotient_card {G : Type*} [Group G] (K : Subgroup G)
    (hmodel : FieldComponentQuotient K) :
    Nat.card (K ⧸ center K) = 20160 ∨ Nat.card (K ⧸ center K) = 604800 ∨
      Nat.card (K ⧸ center K) = 1876896 := by
  unfold FieldComponentQuotient at hmodel
  rcases hmodel with ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · obtain ⟨e⟩ := e
    exact Or.inl ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL)
  · obtain ⟨e⟩ := e
    exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier))
  · obtain ⟨e⟩ := e
    right; right
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective (ZMod 7)]
    norm_num [Nat.card_zmod]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.CoverModels
