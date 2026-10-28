module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction

/-!
# Order separation for the terminal triple covers

The order 7560 of the triple cover of A₇ is absent from the actual B.5.6
component list. Its two-part bounds the binary field parameters, and the
remaining small orders differ. The divisors 1080 and 7560 also exclude
B.5.1's proper symmetric and binary G₂ actor extensions.

These are comparisons of actual model equivalences, not recognition by
order. The cover and offender applications are in `TripleRows`.
Source: Aschbacher–Smith, B.5.1/B.5.6, pp.99–105, F.6.18, pp.309–310,
and the terminal proof of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.TripleRows
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card SL(d,F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(d,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card SL(3,F) * (q - 1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h]
  ring

private theorem power_bound {k : ℕ} (h : 2 ^ k ∣ 7560) : k ≤ 3 := by
  by_contra hn
  have h16 : 16 ∣ 7560 := (pow_dvd_pow 2 (show 4 ≤ k by omega)).trans h
  norm_num at h16

/-- The actual component catalogue has no group of order 7560. -/
theorem model_card_ne_7560 {A : Type*} [Group A]
    (h : QuasisimpleModel A) : Nat.card A ≠ 7560 := by
  intro hc
  cases h with
  | linearTwo F e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have hd : 2 ^ F.degree ∣ 7560 := by
      rw [← he, Atlas.card_sl_two, F.card_eq]
      exact dvd_mul_right _ _
    have hb := power_bound hd
    have hp := F.degree_pos
    rw [Atlas.card_sl_two, F.card_eq] at he
    interval_cases h : F.degree <;> norm_num [h] at he
  | linearThree F e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have hd : 2 ^ (F.degree * 3) ∣ 7560 := by
      rw [← he, sl_three_card, F.card_eq, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hb := power_bound hd
    have hp := F.degree_pos
    have h : F.degree = 1 := by omega
    rw [sl_three_card, F.card_eq, h] at he
    norm_num at he
  | symplecticFour F e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have hd : 2 ^ (F.degree * 4) ∣ 7560 := by
      rw [← he, Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have := power_bound hd
    have := F.degree_pos
    omega
  | g2 F e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have hd : 2 ^ (F.degree * 6) ∣ 7560 := by
      rw [← he, Atlas.G2.card_Model, F.card_eq, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have := power_bound hd
    have := F.degree_pos
    omega
  | alternatingSix e =>
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  | alternatingSeven e =>
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  | tripleSix ec eq =>
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A),
      Nat.card_congr ec.toEquiv, Nat.card_congr eq.toEquiv,
      nat_card_alternatingGroup] at hc
    norm_num [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.factorial] at hc
  | g2DerivedTwo e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have ho := Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
    change Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 at ho
    omega
  | linearFourTwo e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have ho := sl_card_mul (ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at ho
    omega
  | linearFiveTwo e =>
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have ho := sl_card_mul (ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at ho
    omega

/-- Neither covering component embeds in an allowed symmetric actor. -/
theorem not_symmetric_actor {A I : Type*} [Group A] [Group I]
    (hc : Nat.card A = 1080 ∨ Nat.card A = 7560)
    (f : A →* I) (hf : Function.Injective f)
    {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8) (e : I ≃* Equiv.Perm (Fin n)) : False := by
  have hd := card_dvd_of_injective f hf
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
    Fintype.card_fin] at hd
  rcases hc with hc | hc <;> rw [hc] at hd <;>
    interval_cases n <;> norm_num [Nat.factorial] at hd

/-- Neither covering component embeds in the allowed full binary G₂ actor. -/
theorem not_g2_actor {A I : Type*} [Group A] [Group I]
    (hc : Nat.card A = 1080 ∨ Nat.card A = 7560)
    (f : A →* I) (hf : Function.Injective f)
    (e : I ≃* Atlas.G2.Model (ZMod 2)) : False := by
  have hd := card_dvd_of_injective f hf
  rw [Nat.card_congr e.toEquiv,
    Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hd
  rcases hc with hc | hc <;> rw [hc] at hd <;> norm_num at hd

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.TripleRows
