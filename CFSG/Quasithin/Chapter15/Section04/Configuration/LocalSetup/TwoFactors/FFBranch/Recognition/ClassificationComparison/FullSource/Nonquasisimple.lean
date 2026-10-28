module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.Basic
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.ExtraspecialFFComparison
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.FFSpectrum

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
universe u v
variable {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal

private theorem quasisimple_not_solvable {A : Type*} [Group A]
    (h : IsQuasisimple A) : ¬ Group.IsSolvable A := by
  let := h
  let : IsSimpleGroup (A ⧸ center A) := h.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  exact Group.IsPerfect.not_isSolvable A

private theorem no_extraspecial_row (h : ClassifiedAction K ρ G₁ G₂)
    (N : Subgroup D) [N.Normal] [IsExtraspecial 3 N] (hN : Nat.card N = 27)
    (e : (D ⧸ N) ≃* FSource.E4) : False := by
  have hD : Nat.card D = 108 := by
    rw [card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv, hN]
    norm_num [FSource.E4,FSource.C,Nat.card_prod]
  have hi : Nat.card (offenderSubgroup ρ) ≤ 108 := by
    rw [← hD]
    exact Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype Subtype.val_injective
  have hQ : IsPGroup 2 (D ⧸ N) :=
    (IsPGroup.of_card (p := 2) (n := 2) (G := FSource.E4)
      (by simp [FSource.E4,FSource.C])).of_equiv e.symm
  cases h.ffAlternatives with
  | trivial ht =>
    let := ht
    let : Nontrivial (offenderSubgroup ρ) := nontrivial_of_ff _ h.ffWitness
    obtain ⟨x,hx⟩ := exists_ne (1 : offenderSubgroup ρ)
    exact hx (Subsingleton.elim _ _)
  | quasisimple hq _ =>
    let : Group.IsNilpotent N := (IsExtraspecial.isPGroup 3 N).isNilpotent
    let : Group.IsNilpotent (D ⧸ N) := hQ.isNilpotent
    let : Group.IsSolvable D :=
      (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,inferInstance⟩
    exact quasisimple_not_solvable hq inferInstance
  | symmetricThree c =>
    exact NormalSymmetricThreeExtraspecial.no_normal_symmetricThree N
      (offenderSubgroup ρ) hQ c.equiv
  | twoFactors c =>
    obtain ⟨a⟩ := LowRows.Extraspecial.product_equiv_symmetricThreePair c.product
      (c.firstCase.factorModel _) (c.secondCase.factorModel _) hi
    exact NormalSymmetricThreeExtraspecial.no_normal_symmetricThreePair N
      (offenderSubgroup ρ) (IsExtraspecial.isPGroup 3 N)
      (IsExtraspecial.center_order_p 3 N) hQ a
  | outerSixThree c =>
    have := c.card_ge
    omega
  | hyperplane c =>
    have hh := (Nat.card_le_card_of_injective c.first.subtype c.first.subtype_injective).trans hi
    rw [Nat.card_congr c.firstEquiv.toEquiv,Matrix.PSL3Two.card_SL] at hh
    omega

private theorem no_prime_product (h : ClassifiedAction K ρ G₁ G₂)
    {S : Sylow 2 D} (r : FSource.ProductRow S) (hs : Nonempty (S ≃* DihedralGroup 4)) :
    False := by
  have h8 : Nat.card S = 8 := by
    rw [Nat.card_congr hs.some.toEquiv,DihedralGroup.nat_card]
  have h16 : ¬ 16 ∣ Nat.card (offenderSubgroup ρ) := by
    intro hd
    have hd' := S.pow_dvd_card_of_pow_dvd_card (show 2^4 ∣ Nat.card D from
      hd.trans (offenderSubgroup ρ).card_subgroup_dvd_card)
    rw [h8] at hd'
    norm_num at hd'
  have ho : Odd r.field.prime := Nat.odd_iff.mpr (by have := r.congruence; omega)
  have hc : Nat.card r.field.Carrier = r.field.prime := by
    rw [r.field.card,r.degree,pow_one]
  have hd : r.field.prime ∣ Nat.card D := by
    have hp : r.field.prime ∣ Nat.card PSL(2,r.field.Carrier) := by
      apply (Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_right
      rw [Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hc ▸ ho),hc]
      exact dvd_mul_right _ _
    rw [← Nat.card_congr r.firstEquiv.toEquiv] at hp
    exact hp.trans r.first.card_subgroup_dvd_card
  have hn := (h.odd_dvd_offender_card_iff ho).mpr hd
  have hle : r.field.prime ≤ 7 := by
    cases h.ffAlternatives with
    | outerSixThree c =>
      exact LowRows.PrimeProduct.FFSpectrum.outerShape_prime_le_seven
        _ h.ffHypothesis.generated c r.field.prime_isPrime hn
    | trivial c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        _ h.ffHypothesis.generated h16 (.trivial c) _ r.field.prime_isPrime hn
    | quasisimple hq c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        _ h.ffHypothesis.generated h16 (.quasisimple hq c) _ r.field.prime_isPrime hn
    | symmetricThree c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        _ h.ffHypothesis.generated h16 (.symmetricThree c) _ r.field.prime_isPrime hn
    | twoFactors c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        _ h.ffHypothesis.generated h16 (.twoFactors c) _ r.field.prime_isPrime hn
    | hyperplane c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        _ h.ffHypothesis.generated h16 (.hyperplane c) _ r.field.prime_isPrime hn
  have := r.congruence
  omega

private theorem nonquasisimple_alternative (h : ClassifiedAction K ρ G₁ G₂)
    (hq : ¬ IsQuasisimple (generalizedFitting D)) {A B : Subgroup D} {S : Sylow 2 D}
    (hcores : pCore 2 A ≠ ⊥ ∨ pCore 2 B ≠ ⊥) (r : FSource.Alternative A B S) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  cases r with
  | one _ ha hb _ => exact (hcores.elim (· ha) (· hb)).elim
  | two hm =>
    rcases hm with hm | ⟨N,_,hN,hcard,_,⟨e⟩⟩
    · exact hm
    · let := hN
      exact (no_extraspecial_row h N hcard e).elim
  | three r hs _ _ => exact (no_prime_product h r hs).elim
  | four _ _ _ _ _ h _ _ _ => exact (hq h).elim
  | five _ _ _ _ _ h _ _ _ => exact (hq h).elim
  | six _ _ h _ _ _ => exact (hq h).elim
  | seven _ h _ _ _ => exact (hq h).elim
  | eight _ h _ _ _ => exact (hq h).elim
  | nine _ h _ _ _ => exact (hq h).elim
  | ten _ _ _ _ _ h _ _ _ => exact (hq h).elim
  | eleven _ h _ _ _ => exact (hq h).elim
  | twelve _ h _ _ _ => exact (hq h).elim
  | thirteen _ _ h _ _ _ => exact (hq h).elim

theorem ClassifiedAction.nonquasisimple_quotient
    (h : ClassifiedAction K ρ G₁ G₂) (hq : ¬ IsQuasisimple (generalizedFitting D)) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rcases h.goldschmidt with hr | hr <;> rcases hr with (hr | r) | r
  · exact nonquasisimple_alternative h hq h.core_nontrivial hr
  · exact (hq r.some.quasisimple).elim
  · exact (hq r.some.quasisimple).elim
  · exact nonquasisimple_alternative h hq h.core_nontrivial.symm hr
  · exact (hq r.some.quasisimple).elim
  · exact (hq r.some.quasisimple).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
