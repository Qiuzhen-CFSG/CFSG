module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.OrderArithmetic
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.EvenSporadicBounds
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.CoverBounds
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import GorensteinWalter.PSL2ProjectiveLine

/-!
# The complete model restriction for the normal A₆ upper component

The original source supplies three bounds on the upper quotient: its order
is divisible by 360, divides |GL₅(2)|, and has two-part at most 32. The full
A.3.6 carrier list then leaves exactly A₆ and A₇. Odd prime divisibility
reduces the PSL₂ rows to the actual field-nine model, and the existing
exceptional isomorphism identifies it with A₆. Root-group orders exclude
the other Lie families; the literal sporadic and three-cover rows use the
shared companion bounds. No new model construction is needed.

This is the model-inspection step for the actual upper quotient constructed
in `SixMaximality.UpperCore`, from the normal A₆ configuration of 13.5.15.
It does not exclude the A₇ alternative or assert maximality of the original L.
Source: Aschbacher–Smith, A.3.6 and 13.3.2, printed pp.43–44,884–885.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.ModelBounds
open Chapter1.Section02.LocalModels OrderArithmetic

variable {G : Type*} [Group G] [Finite G]

private theorem not_sixtyFour_dvd_card (hSyl : ∀ S : Sylow 2 G, Nat.card S ≤ 32) :
    ¬ 64 ∣ Nat.card G := by
  intro hd
  let S : Sylow 2 G := Classical.choice inferInstance
  have hp : 2 ^ 6 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card hd
  have hb := Nat.le_of_dvd (Nat.card_pos (α := S)) hp
  have hs := hSyl S
  norm_num at hb
  omega

private theorem alternating (h360 : 360 ∣ Nat.card G)
    (hSyl : ∀ S : Sylow 2 G, Nat.card S ≤ 32)
    (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8) (hm : IsAlternating G n) :
    IsAlternating G 6 ∨ IsAlternating G 7 := by
  obtain ⟨e⟩ := hm
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hn₀ := hn.1
  have hn₁ := hn.2
  have hc : Nat.card G = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp
  interval_cases n
  · norm_num at hc
    rw [hc] at h360
    norm_num at h360
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩
  · apply False.elim (not_sixtyFour_dvd_card hSyl _)
    rw [hc]
    norm_num

omit [Finite G] in
private theorem linear_odd (h360 : 360 ∣ Nat.card G) (hGL : Nat.card G ∣ 9999360)
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hm : ClassicalGroup.IsPSL G 2 (p ^ e)) : IsAlternating G 6 := by
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
  have hc : Nat.card G * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [Nat.card_congr a.toEquiv]
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (hF.symm ▸ (ho.pow : Odd (p ^ e)))
    rw [hF] at hc
    exact hc
  have hd : p ∣ Nat.card G * 2 := by
    rw [hc]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  have hpn : p ∣ Nat.card G := (hp.dvd_mul.mp hd).resolve_right (by
    intro hd
    have heq : p = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left hp.ne_one
    subst p
    norm_num at ho)
  rcases odd_prime_dvd_gl_five hp ho (hpn.trans hGL) with rfl | rfl | rfl | rfl
  all_goals rcases he with rfl | rfl
  all_goals norm_num at hc hF
  all_goals try
    have hd : 720 ∣ Nat.card G * 2 := Nat.mul_dvd_mul h360 (dvd_refl 2)
    rw [hc] at hd
    norm_num at hd
  exact ⟨a.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF)⟩

omit [Finite G] in
private theorem odd_three (hGL : Nat.card G ∣ 9999360)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign G unitary 3 p) : False := by
  apply odd_cube_not_dvd_gl_five hp ho
  apply dvd_trans _ hGL
  cases unitary
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv, ← hF]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card
  · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_projective hp hF hconj

omit [Finite G] in
private theorem bender (h360 : 360 ∣ Nat.card G) (h64 : ¬ 64 ∣ Nat.card G)
    (hm : ClassificationModels.IsBenderModel G) : False := by
  cases hm with
  | linear f hf hm =>
      obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
      have hq : 2 ^ f ∣ Nat.card G := by
        rw [Nat.card_congr a.toEquiv, ← hF,
          ← GorensteinWalter.psl2UpperUnipotentSubgroup_card F]
        exact card_subgroup_dvd_card _
      have hbound : f ≤ 5 := by
        by_contra hn
        apply h64
        exact (show 2 ^ 6 ∣ 2 ^ f from pow_dvd_pow 2 (by omega)).trans hq
      have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
      rw [← Nat.card_congr a.toEquiv, hF] at hc
      interval_cases f <;> norm_num [Fin.prod_univ_succ] at hc <;> omega
  | unitary f hf hm =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨a⟩⟩ := hm
      apply h64
      have hq := J.cube_dvd_card_projective hF
        (BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.card_fixed J hF hconj)
      rw [← Nat.card_congr a.toEquiv, ← pow_mul] at hq
      exact (show 2 ^ 6 ∣ 2 ^ (f * 3) from pow_dvd_pow 2 (by omega)).trans hq
  | suzuki m hm iso =>
      obtain ⟨a⟩ := iso
      apply BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
      rw [← Nat.card_congr a.toEquiv]
      exact (by norm_num : 3 ∣ 360).trans h360

/-- The complete literal carrier catalogue leaves only A₆ and A₇ under the
three bounds proved for the original normal-A₆ upper component. -/
theorem theoremC_or_threeCover (h360 : 360 ∣ Nat.card G)
    (hGL : Nat.card G ∣ 9999360)
    (hSyl : ∀ S : Sylow 2 G, Nat.card S ≤ 32)
    (hm : TheoremCModel G ∨ ThreeCoverModel G) :
    IsAlternating G 6 ∨ IsAlternating G 7 := by
  have h64 := not_sixtyFour_dvd_card hSyl
  rcases hm with hm | hm
  · cases hm with
    | alternating n hn iso => exact alternating h360 hSyl n hn iso
    | linear_odd p e hp ho he _ iso => exact .inl (linear_odd h360 hGL p e hp ho he iso)
    | three_odd p hp ho unitary iso => exact (odd_three hGL p hp ho unitary iso).elim
    | rank_one iso => exact (bender h360 h64 iso).elim
    | rank_two iso => exact .inl (EvenSporadicBounds.rankTwo_alternatingSix h360 h64 iso)
    | binary_linear n hn iso => exact (EvenSporadicBounds.binary_linear_excluded h64 hn iso).elim
    | sporadic name hne iso =>
        exact (EvenSporadicBounds.sporadic_excluded hGL h64 (.inl ⟨name, hne, iso⟩)).elim
    | janko_one iso => exact (EvenSporadicBounds.sporadic_excluded hGL h64 (.inr iso)).elim
  · exact (CoverBounds.threeCover_excluded h360 hGL h64 hm).elim

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.ModelBounds
