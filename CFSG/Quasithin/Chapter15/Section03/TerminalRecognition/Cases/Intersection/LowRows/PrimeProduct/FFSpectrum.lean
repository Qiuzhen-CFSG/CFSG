module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Reduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.PrimeRow
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.Reduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape

/-!
# Prime support of the terminal FF alternatives

For an offender-generated finite actor whose order is not divisible by sixteen,
all the supplied B.5.6 alternatives have prime divisors at most seven. The
Sylow bound restricts binary SL₂ to field degree at most three and SL₃ to
degree one. The bounded quasisimple and outer-actor models are compared through
their actual group equivalences and concrete order formulas. The literal direct
products are counted factor by factor. In the A₆–C₃ extension, generation by
binary offenders makes the cyclic quotient over the normal product a two-group.

The complete supplied classification conclusion is retained. The proof uses its
group identifications, without using the legacy triple-six offender clause or
the outer case's disputed module splitting. This is a comparison of explicit
classification outputs, not a proof of the universal B.5.6 classifier.

The final adapter applies this comparison to the original terminal offender
representation, using its already proved generation and cardinal restriction.
The parent owns the resulting F.6.18(3) exclusion; importing its reduction
rather than its assembly module keeps that integration acyclic.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
B.5.6, printed pp.99–105; F.6.17–18, printed pp.309–310; and the terminal
intersection in the proof of 15.3.1, printed p.1155.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.LowRows.PrimeProduct.FFSpectrum
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives QuasisimpleComparison

variable {A : Type*} [Group A] [Finite A]

omit [Group A] [Finite A] in
private theorem two_exponent_le_three (h16 : ¬ 16 ∣ Nat.card A)
    {k : ℕ} (hd : 2 ^ k ∣ Nat.card A) : k ≤ 3 := by
  by_contra h
  exact h16 ((Nat.pow_dvd_pow 2 (show 4 ≤ k by omega)).trans hd)

private theorem sylow_card_le_eight (h16 : ¬ 16 ∣ Nat.card A) (S : Sylow 2 A) :
    Nat.card S ≤ 8 := by
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hd : 2 ^ k ∣ Nat.card A := by
    rw [← hk]
    exact (S : Subgroup A).card_subgroup_dvd_card
  rw [hk]
  exact Nat.pow_le_pow_right (by decide) (two_exponent_le_three h16 hd)

private theorem prime_le_seven_of_dvd {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 120960) : p ≤ 7 := by
  rw [show (120960 : ℕ) = 2^7 * 3^3 * 5 * 7 by decide] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hd)).trans (by decide)
      · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hd)).trans (by decide)
    · exact (Nat.le_of_dvd (by decide) hd).trans (by decide)
  · exact Nat.le_of_dvd (by decide) hd

private theorem factor_card_dvd (h16 : ¬ 16 ∣ Nat.card A)
    {B : Type*} [Group B] (h : FactorModel B) (f : B →* A)
    (hf : Function.Injective f) : Nat.card B ∣ 120960 := by
  let S : Sylow 2 A := Classical.choice inferInstance
  exact (ProductComparison.factor_card_dvd_of_sylow_eight h f hf S
    (sylow_card_le_eight h16 S)).trans (by decide)

private theorem bounded_quasisimple_card_dvd (h16 : ¬ 16 ∣ Nat.card A)
    (h : BoundedQuasisimpleModel A) : Nat.card A ∣ 120960 := by
  cases h with
  | linearTwo F _ _ e =>
    exact factor_card_dvd h16 (.linearTwo F e) (MonoidHom.id A) Function.injective_id
  | linearThree F _ e =>
    have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, ← pow_mul] at hd
    have hb : F.degree * 3 ≤ 3 := two_exponent_le_three h16 (by
      rwa [Nat.card_congr e.toEquiv])
    have he : F.degree = 1 := by have := F.degree_pos; omega
    exact factor_card_dvd h16 (.linearThree F (by rw [he]; decide) e)
      (MonoidHom.id A) Function.injective_id
  | alternatingSix e =>
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | alternatingSeven e =>
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | tripleSix e a =>
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A),
      Nat.card_congr a.toEquiv, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | g2DerivedTwo e =>
    rw [Nat.card_congr e.toEquiv, Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]
    decide
  | linearFourTwo e =>
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.val_zero, Fin.val_succ, Nat.mul_one] at hc
    have hd : 16 ∣ Nat.card PSL(4,ZMod 2) := by rw [hc]; decide
    apply (h16 ?_).elim
    rw [Nat.card_congr e.toEquiv]
    exact hd.trans (card_dvd_of_surjective (QuotientGroup.mk' (center SL(4,ZMod 2)))
      (QuotientGroup.mk'_surjective _))

private theorem bounded_actor_card_dvd (h16 : ¬ 16 ∣ Nat.card A)
    (h : BoundedActorModel A) : Nat.card A ∣ 120960 := by
  rcases h with h | h
  · exact bounded_quasisimple_card_dvd h16 h
  rcases h with ⟨n, hlo, hhi, ⟨e⟩⟩ | ⟨e⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    interval_cases n <;> norm_num [Nat.factorial]
  · obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv, Atlas.G2.LieAutomorphismExtensions.card_binaryFull]
    decide

private theorem product_prime_le_seven (h16 : ¬ 16 ∣ Nat.card A)
    {B C : Subgroup A} (c : InternalProduct B C) (hB : FactorModel B)
    (hC : FactorModel C) {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card A) : p ≤ 7 := by
  rw [← Nat.card_congr c.equiv.toEquiv, Nat.card_prod] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact prime_le_seven_of_dvd hp
      (hd.trans (factor_card_dvd h16 hB B.subtype B.subtype_injective))
  · exact prime_le_seven_of_dvd hp
      (hd.trans (factor_card_dvd h16 hC C.subtype C.subtype_injective))

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem outer_prime_le_seven (ρ : Representation (ZMod 2) A W)
    (hgen : offenderSubgroup ρ = ⊤) (c : OuterSixThreeCase ρ)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card A) : p ≤ 7 := by
  let := c.product_normal ρ
  let := c.quotient_isCyclic ρ
  let := IsCyclic.commGroup (α := A ⧸ (c.first ⊔ c.second))
  have hq := abelian_image_isTwoGroup ρ (QuotientGroup.mk' (c.first ⊔ c.second))
    (QuotientGroup.mk'_surjective _) hgen
  have hc : Nat.card (c.first ⊔ c.second : Subgroup A) = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨k, hk⟩ := hq.exists_card_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (c.first ⊔ c.second), hk, hc] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hd)).trans (by decide)
  · exact prime_le_seven_of_dvd hp (hd.trans (by decide))

/-- The same prime-support estimate for the source-corrected group-only
outer A₆--C₃ configuration.  The product and cyclic quotient are the actual
subgroups from the source record; no module splitting is used. -/
theorem outerShape_prime_le_seven (ρ : Representation (ZMod 2) A W)
    (hgen : offenderSubgroup ρ = ⊤) (c : ChapterB.OuterSixThreeShape A)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card A) : p ≤ 7 := by
  let := FFAlternatives.outerSixThreeShape_product_normal c
  let := FFAlternatives.outerSixThreeShape_quotient_isCyclic c
  let := IsCyclic.commGroup (α := A ⧸ (c.first ⊔ c.second))
  have hq := abelian_image_isTwoGroup ρ (QuotientGroup.mk' (c.first ⊔ c.second))
    (QuotientGroup.mk'_surjective _) hgen
  have hc : Nat.card (c.first ⊔ c.second : Subgroup A) = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨k, hk⟩ := hq.exists_card_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (c.first ⊔ c.second), hk, hc] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hd)).trans (by decide)
  · exact prime_le_seven_of_dvd hp (hd.trans (by decide))

/-- The complete supplied FF alternatives, with offender generation and two-part
at most eight, allow no prime divisor greater than seven. -/
theorem prime_le_seven (ρ : Representation (ZMod 2) A W)
    (hgen : offenderSubgroup ρ = ⊤) (h16 : ¬ 16 ∣ Nat.card A)
    (hB : SourceAlternative ρ) : ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p ≤ 7 := by
  intro p hp hd
  cases hB with
  | trivial ht =>
    let : Subsingleton A := ht
    rw [Nat.card_unique] at hd
    exact (hp.not_dvd_one hd).elim
  | quasisimple hq c =>
    have hs : ∀ S : Sylow 2 A, Nat.card S ≤ 128 :=
      fun S => (sylow_card_le_eight h16 S).trans (by decide)
    have hm := (bounded_actor hs (MonoidHom.id A) Function.injective_id ρ hq c).2
    exact prime_le_seven_of_dvd hp (hd.trans (bounded_actor_card_dvd h16 hm))
  | symmetricThree c =>
    apply prime_le_seven_of_dvd hp
    apply hd.trans
    rw [Nat.card_congr c.equiv.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  | twoFactors c =>
    exact product_prime_le_seven h16 c.product (c.firstCase.factorModel ρ)
      (c.secondCase.factorModel ρ) hp hd
  | outerSixThree c => exact outer_prime_le_seven ρ hgen c hp hd
  | hyperplane c =>
    exact product_prime_le_seven h16 c.product
      (.linearThree BinaryField.two (by decide) c.firstEquiv)
      (c.secondCase.factorModel ρ) hp hd

/-- The prime-support estimate for the corrected projective-line source
alternative.  The quasisimple branch uses the corrected bounded-actor
comparison, while the outer branch is handled by its literal group shape. -/
theorem prime_le_seven_projectiveLine (ρ : Representation (ZMod 2) A W)
    (hgen : offenderSubgroup ρ = ⊤) (h16 : ¬ 16 ∣ Nat.card A)
    (hB : FFAlternatives.ProjectiveLine.SourceAlternative ρ) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p ≤ 7 := by
  intro p hp hd
  cases hB with
  | trivial ht =>
    let : Subsingleton A := ht
    rw [Nat.card_unique] at hd
    exact (hp.not_dvd_one hd).elim
  | quasisimple hq c =>
    have hs : ∀ S : Sylow 2 A, Nat.card S ≤ 128 :=
      fun S => (sylow_card_le_eight h16 S).trans (by decide)
    have hm := QuasisimpleComparison.projectiveLine_bounded_actor hs
      (MonoidHom.id A) Function.injective_id ρ hq c
    exact prime_le_seven_of_dvd hp (hd.trans (bounded_actor_card_dvd h16 hm.2))
  | symmetricThree c =>
    exact prime_le_seven ρ hgen h16 (.symmetricThree c) p hp hd
  | twoFactors c =>
    exact prime_le_seven ρ hgen h16 (.twoFactors c) p hp hd
  | outerSixThree c =>
    exact outerShape_prime_le_seven ρ hgen c.toGroupShape hp hd
  | hyperplane c =>
    exact prime_le_seven ρ hgen h16 (.hyperplane c) p hp hd

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.LowRows.PrimeProduct.FFSpectrum

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Apply the complete FF comparison to the original terminal offender action. -/
theorem primeProduct_offender_prime_le_seven
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4))
    (hB : FFAlternatives.SourceAlternative d.offenderAction) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card d.offenderGroup → p ≤ 7 :=
  LowRows.PrimeProduct.FFSpectrum.prime_le_seven d.offenderAction
    d.primeProduct_offender_generated (d.primeProduct_no_sixteen_dvd_offender hs) hB

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
