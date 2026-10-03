module

public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionPreliminaries
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionMass
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOddFiberCard

/-!
# The actual ambient Lyons section masses

The equation (3.1) expansion computes the mass on the genuine centralizer.
Inflation through its odd core preserves the normalized odd-element sum, and
the supplied quotient isomorphism transports it to the explicit local group.
This step retains both the odd core and the prescribed enumeration of the
five linear characters.

The proved local fiber counts (one over the identity and sixteen over each
nonidentity complement element) give the involution numerator in (3.3).
Adding the already proved order-four mass gives the combined numerator.
The final formulas use the compatible action in the supplied model to
discharge the counting hypothesis; they assume no Gram identity or section norm.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373–374,
equations (3.1) and (3.3).
-/

public section

noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup ModularBlock PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G]

/-- Inflation through the actual odd core preserves the section norm. -/
theorem FiveSectionModel.section_mass_eq_local_odd_norm
    {S : Sylow 2 G} {z : G} (M : FiveSectionModel S z)
    (χ : ClassFunction G) (a : Fin 5 → ℤ)
    (he : ∀ v : centralizer ({z} : Set G), Odd (orderOf v) →
      χ (z * (v : G)) = ∑ i, (a i : ℂ) * M.mu v ^ GeneralizedDecompositionData.basicExponent i) :
    Theory.Character.twoSectionMass χ z =
      Cartan.normalizedOddNorm (fun u : LocalFiveGroup S M.α =>
        ∑ i, (a i : ℂ) * M.enumeration i u.right) := by
  let C := centralizer ({z} : Set G)
  let N := pPrimeCore 2 C
  have hN : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  calc
    Theory.Character.twoSectionMass χ z = Cartan.normalizedOddNorm
        (fun v : C => ∑ i, (a i : ℂ) * M.mu v ^ GeneralizedDecompositionData.basicExponent i) :=
      TwoSectionContribution.mass_eq_normalizedOddNorm χ z _ he
    _ = OddElementSum.normalized (fun v : C =>
        Complex.normSq (∑ i, (a i : ℂ) *
          M.enumeration i (M.quotientEquiv (QuotientGroup.mk' N v)).right)) := by
      apply OddElementSum.normalized_congr
      intro v _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [M.enumeration_apply, M.mu_apply, MonoidHom.pow_apply]
    _ = OddElementSum.normalized (fun q : C ⧸ N =>
        Complex.normSq (∑ i, (a i : ℂ) * M.enumeration i (M.quotientEquiv q).right)) :=
      OddElementSum.normalized_odd_quotient N hN
        (fun q : C ⧸ N => Complex.normSq
          (∑ i, (a i : ℂ) * M.enumeration i (M.quotientEquiv q).right))
    _ = _ := OddElementSum.normalized_equiv M.quotientEquiv
      (fun u : LocalFiveGroup S M.α => Complex.normSq (∑ i, (a i : ℂ) * M.enumeration i u.right))

/-- The involution mass from the actual local odd-element fiber counts. -/
theorem ambient_involution_mass_of_fiber_card
    (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G) (t : S)
    (M : FiveSectionModel S ((t : G)^2))
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) (t : G) ((t : G)^2) M.mu)
    (hcount : ∀ x : FiveComplement,
      Nat.card {u : LocalFiveGroup S M.α // Odd (orderOf u) ∧ u.right = x} =
        if x = 1 then 1 else 16)
    (j : {i // i ∈ b.block}) :
    Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) ((t : G)^2) =
      (((∑ i, c.iDz i j ^ 2) +
        3 * ∑ i, ∑ k ∈ Finset.Iio i, (c.iDz k j - c.iDz i j)^2 : ℤ) : ℝ) / 64 := by
  rw [M.section_mass_eq_local_odd_norm _ (fun i => c.iDz i j) (he.2 j)]
  exact localFive_normalizedOddNorm_of_fiber_card S M.α h hcount M.enumeration _

/-- Adding the two genuine section masses gives the contribution numerator. -/
theorem ambient_combined_mass_of_fiber_card
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4)
    (M : FiveSectionModel S ((t : G)^2))
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) (t : G) ((t : G)^2) M.mu)
    (hcount : ∀ x : FiveComplement,
      Nat.card {u : LocalFiveGroup S M.α // Odd (orderOf u) ∧ u.right = x} =
        if x = 1 then 1 else 16)
    (j : {i // i ∈ b.block}) :
    Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) (t : G) +
      Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) ((t : G)^2) =
        (c.contribution j : ℝ) / 64 := by
  rw [ambient_orderFour_mass S d b t ht M.mu c he j,
    ambient_involution_mass_of_fiber_card S h b t M c he hcount j]
  unfold GeneralizedDecompositionData.contribution
  push_cast
  ring

/-- The actual involution section mass in Lyons's equation (3.3). -/
theorem ambient_involution_mass
    (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G) (t : S)
    (M : FiveSectionModel S ((t : G)^2))
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) (t : G) ((t : G)^2) M.mu)
    (j : {i // i ∈ b.block}) :
    Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) ((t : G)^2) =
      (((∑ i, c.iDz i j ^ 2) +
        3 * ∑ i, ∑ k ∈ Finset.Iio i, (c.iDz k j - c.iDz i j)^2 : ℤ) : ℝ) / 64 := by
  exact ambient_involution_mass_of_fiber_card S h b t M c he
    (localFive_odd_fiber_card S h M.β M.order_β M.α M.action) j

/-- The actual order-four and involution section masses sum to the contribution. -/
theorem ambient_combined_mass
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4)
    (M : FiveSectionModel S ((t : G)^2))
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) (t : G) ((t : G)^2) M.mu)
    (j : {i // i ∈ b.block}) :
    Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) (t : G) +
      Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) ((t : G)^2) =
        (c.contribution j : ℝ) / 64 := by
  exact ambient_combined_mass_of_fiber_card S h d b t ht M c he
    (localFive_odd_fiber_card S h M.β M.order_β M.α M.action) j
end Stellmacher.Recognition.LyonsU3Four
