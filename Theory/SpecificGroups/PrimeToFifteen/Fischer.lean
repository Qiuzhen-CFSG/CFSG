module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Evaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.ComparisonA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.ComparisonB
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement
public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.GroupTheory.Coset.Card
/-!
# Three-divisibility of the three literal Fischer carriers

A point with period three forces a factor three in the order of its acting group.
The actual Fi₂₃ and Fi₂₄′ second generators have such cycles. For Fi₂₂ the word
`B * A * B² * A` has the marked cycle `(35,1078,703)`. Existing certified lookup
maps identify each evaluation with the original inverse ATLAS cycle product.
Only these nine point evaluations are computed; no order formula or recognition
hypothesis is required, and no new permutation table is introduced.

Source: ATLAS `F22G1-p3510B0`, `F23G1-p31671B0`, and `F24G1-p306936B0`,
retained in the imported carriers. Application: Aschbacher–Smith 1.1.5(3),
used in the known-simple prime-to-15 argument and 15.3.34.
-/

public section

-- Keep the point certificates sequential while importing the large source tables.
set_option Elab.async false

private theorem prime_dvd_of_point {G X : Type*} [Group G]
    (f : G →* Equiv.Perm X) (g : G) (x : X) (p : ℕ) [Fact p.Prime]
    (hc : (f g ^ p) x = x) (hn : f g x ≠ x) : p ∣ Nat.card G := by
  have hd : MulAction.period (f g) x ∣ p :=
    MulAction.pow_smul_eq_iff_period_dvd.mp hc
  have hp : MulAction.period (f g) x = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
    · exact (hn (MulAction.period_eq_one_iff.mp h)).elim
    · exact h
  have hmap : orderOf (f g) ∣ orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  exact (hp ▸ MulAction.period_dvd_orderOf (f g) x).trans
    (hmap.trans (orderOf_dvd_natCard g))


private theorem three_dvd_of_cycle {X : Type*} (S : Subgroup (Equiv.Perm X))
    (g : Equiv.Perm X) (hg : g ∈ S) (a b c : X)
    (hab : g a = b) (hbc : g b = c) (hca : g c = a) (hne : b ≠ a) :
    3 ∣ Nat.card S := by
  let u : S := ⟨g, hg⟩
  apply prime_dvd_of_point S.subtype u a 3
  · change (g ^ 3) a = a
    simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hab, hbc, hca]
  · exact hne ∘ hab.symm.trans

namespace Sporadic.Fischer.Fi23
open CentralizerSection.CandidateCertificate
private theorem step0 : generatorB (0 : Fin 31671) = 25453 := by
  rw [generatorB_apply]
  decide +kernel
private theorem step1 : generatorB (25453 : Fin 31671) = 9469 := by
  rw [generatorB_apply]
  decide +kernel
private theorem step2 : generatorB (9469 : Fin 31671) = 0 := by
  rw [generatorB_apply]
  decide +kernel
/-- Three divides the order of the actual published Fischer carrier. -/
theorem three_dvd_card : 3 ∣ Nat.card Carrier :=
  three_dvd_of_cycle generated generatorB (Subgroup.subset_closure (by simp))
    0 25453 9469 step0 step1 step2 (by decide)
end Sporadic.Fischer.Fi23

namespace Sporadic.Fischer.Fi24Prime
open Fi23Lift.Certificate.Ambient
private theorem step0 : generatorB (0 : Fin 306936) = 89495 := by
  rw [← bMap_correct]
  decide +kernel
private theorem step1 : generatorB (89495 : Fin 306936) = 177570 := by
  rw [← bMap_correct]
  decide +kernel
private theorem step2 : generatorB (177570 : Fin 306936) = 0 := by
  rw [← bMap_correct]
  decide +kernel
/-- Three divides the order of the actual published Fischer carrier. -/
theorem three_dvd_card : 3 ∣ Nat.card Carrier :=
  three_dvd_of_cycle generated generatorB (Subgroup.subset_closure (by simp))
    0 89495 177570 step0 step1 step2 (by decide)
end Sporadic.Fischer.Fi24Prime

namespace Sporadic.Fischer.Fi22
private def word : Equiv.Perm (Fin 3510) := generatorB * generatorA * generatorB ^ 2 * generatorA
private def pointMap (x : Fin 3510) : Fin 3510 :=
  KernelCertificate.fastB (KernelCertificate.fastA
    (KernelCertificate.fastB (KernelCertificate.fastB (KernelCertificate.fastA x))))
private theorem word_evaluate {X : Type*} (a b : Equiv.Perm X) (fa fb : X → X)
    (ha : ∀ x, a x = fa x) (hb : ∀ x, b x = fb x) (x : X) :
    (b * a * b ^ 2 * a) x = fb (fa (fb (fb (fa x)))) := by
  simp only [pow_two, Equiv.Perm.mul_apply, ha, hb]
private theorem word_apply (x : Fin 3510) : word x = pointMap x :=
  word_evaluate generatorA generatorB KernelCertificate.fastA KernelCertificate.fastB
    KernelCertificate.generatorA_apply_eq_fastA KernelCertificate.generatorB_apply_eq_fastB x
private theorem word_mem : word ∈ generated := by
  have ha : generatorA ∈ generated := Subgroup.subset_closure (by simp)
  have hb : generatorB ∈ generated := Subgroup.subset_closure (by simp)
  exact generated.mul_mem (generated.mul_mem (generated.mul_mem hb ha)
    (generated.pow_mem hb 2)) ha
private theorem step0 : word (35 : Fin 3510) = 1078 := by
  rw [word_apply]
  decide +kernel
private theorem step1 : word (1078 : Fin 3510) = 703 := by
  rw [word_apply]
  decide +kernel
private theorem step2 : word (703 : Fin 3510) = 35 := by
  rw [word_apply]
  decide +kernel
/-- Three divides the order of the actual published Fischer carrier. -/
theorem three_dvd_card : 3 ∣ Nat.card Carrier :=
  three_dvd_of_cycle generated word word_mem 35 1078 703 step0 step1 step2 (by decide)
end Sporadic.Fischer.Fi22
