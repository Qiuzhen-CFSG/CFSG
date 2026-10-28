module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.SpecificGroups.ThreeDivisibility.Exceptional
public import Theory.SpecificGroups.ThreeDivisibility.Sporadic
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order

/-!
# Suzuki identification of the three-prime C-components in 13.6.27

Apply the complete universal A.3.6 implication to the actual component image
in H/O₂(H). Every nonsuzuki entry in its full Theorem C catalogue has order
divisible by three. The cover case has a center of order three; both nonsimple
cases have an actual SL₂ quotient, which also has a three divisor. Hence a
component of three-prime order must have a Suzuki image. The canonical
C-component quotient equivalence identifies that image with D/O₂(D).

The matrix, exceptional and sporadic cases reuse concrete three-divisibility
proofs. The additional odd-characteristic U₃ case adapts the cyclic matrix
argument of `Theory.SpecificGroups.ThreeDivisibility.Classical` after transport
to an orthonormal Hermitian basis. J₁ uses its certified generator of order
three. Neither full model simplicity nor a new order formula is needed.

The sole earlier classification assumption is the complete universal A.3.6
implication, whose producer is `qt-a03-sqtk-structure`. Its final discharge
belongs to the source assembly. This module proves the independent conditional
catalogue deduction, including the literal quotient specialization consumed by
`SuzukiIsolation.hz_component_obstruction`; it does not import that parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Theorem C and
Remark A.2.4 (p.33), A.3.6 (pp.43–45), and the Suzuki step of 13.6.27,
printed p.934 / PDF p.951 (`refs/quasithin.pdf`).
-/

public section

open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
open Chapter1.Section02 Chapter1.Section02.LocalModels ClassificationModels
open Theory.SpecificGroups.ThreeDivisibility
universe u
variable {F : Type*} [Field F]
private def cycleLift : SL(3,F) :=
  ⟨!![0,0,1;1,0,0;0,1,0], by simp [Matrix.det_fin_three]⟩
private theorem cycleLift_cube : (cycleLift (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (cycleLift (F := F)).val ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleLift, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
private theorem cycleLift_noncentral : cycleLift (F := F) ∉ center SL(3,F) := by
  intro h
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 0) hr
  simp [cycleLift] at hh

private theorem identity_exists_three (J : HermitianForm 3 F) (hJ : J.form = 1) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J, orderOf x = 3 := by
  let A := SpecialLinearGroup.toGL (cycleLift (F := F))
  have hA : A ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · rw [hJ, mul_one]
      change J.conjTranspose (cycleLift (F := F)).val * (cycleLift (F := F)).val = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cycleLift, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
    · apply Units.ext
      exact (cycleLift (F := F)).property
  let x : ProjectiveSpecialUnitaryMatrixGroup J := ⟨ProjGenLinGroup.mk A, ⟨A,hA,rfl⟩⟩
  refine ⟨x, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    change (ProjGenLinGroup.mk A) ^ 3 = 1
    rw [← map_pow]
    change ProjGenLinGroup.mk ((SpecialLinearGroup.toGL (cycleLift (F := F))) ^ 3) = 1
    rw [← map_pow, cycleLift_cube, map_one, map_one]
  · intro hx
    have hh := congrArg Subtype.val hx
    change ProjGenLinGroup.mk A = 1 at hh
    exact cycleLift_noncentral ((SpecialLinearGroup.toGL_mem_center_iff _).mp
      (ProjGenLinGroup.mk_eq_one.mp hh))

private theorem unitary_prime_three_dvd [Finite F] (J : HermitianForm 3 F)
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card F = p^2)
    (hconj : ∀ x, J.conj x = x^p) :
    3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
    (by decide) (by simpa using hcard) (by simpa using hconj)
  simp only [pow_one] at hfixed
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    3 J p hcard hfixed
  let e := HermitianForm.IdentityGram.projectiveEquiv J C hC
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨x, hx⟩ := identity_exists_three (HermitianForm.IdentityGram.identityGram J) rfl
  simpa only [hx] using _root_.orderOf_dvd_natCard x

variable {K : Type*} [Group K]

private theorem linear {n q : ℕ} (hn : 2 ≤ n) (h : ClassicalGroup.IsPSL K n q) :
    3 ∣ Nat.card K := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F n hn

private theorem special_linear_two (F : Type*) [Field F] :
    3 ∣ Nat.card SL(2,F) :=
  (Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)).trans
    (center SL(2,F)).card_quotient_dvd_card

private theorem unitary_binary {f : ℕ} (hf : 0 < f)
    (h : ClassicalGroup.IsPSU K 3 (2 ^ f)) : 3 ∣ Nat.card K := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact unitary_three_dvd J f hf hcard hconj

private theorem g2_model {q : ℕ} (h : IsG2At K q) : 3 ∣ Nat.card K := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact g2 F

private theorem bender (h : IsBenderModel K) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) ∨ 3 ∣ Nat.card K := by
  cases h with
  | linear f _ iso => exact Or.inr (linear (by decide) iso)
  | unitary f hf iso => exact Or.inr (unitary_binary (by omega) iso)
  | suzuki m hm iso => exact Or.inl ⟨m, hm, iso⟩

private theorem rank_two (h : RankTwoTheoremC K) : 3 ∣ Nat.card K := by
  cases h with
  | linear f _ iso => exact linear (by decide) iso
  | symplectic f _ iso =>
      obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact symplectic F hcard
  | g2 f _ iso => exact g2_model iso
  | triality f _ iso => exact Triality.Standard.model_three_dvd_card iso
  | ree m _ iso =>
      obtain ⟨d, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact ReeF4.LocalBlockInput.three_dvd_card d
  | symplectic_derived iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact symplectic_derived
  | g2_derived iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact g2_derived
  | tits iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact tits

private theorem sporadic_three_dvd (name : SporadicName) (hne : name ≠ .j3) :
    3 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 => change 3 ∣ Nat.card Sporadic.Mathieu.M11; rw [Sporadic.Mathieu.m11_order]; decide
  | m12 => change 3 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; decide
  | m22 => change 3 ∣ Nat.card Sporadic.Mathieu.M22; rw [Sporadic.Mathieu.m22_order]; decide
  | m23 => change 3 ∣ Nat.card Sporadic.Mathieu.M23; rw [Sporadic.Mathieu.m23_order]; decide
  | m24 => change 3 ∣ Nat.card Sporadic.Mathieu.M24; rw [Sporadic.Mathieu.m24_order]; decide
  | j2 => exact j2
  | j3 => exact (hne rfl).elim
  | j4 => exact j4
  | hs => exact hs
  | he => exact held
  | ru => exact rudvalis

/-- Every entry in the complete Theorem C catalogue is Suzuki or has order
    divisible by three, using its actual model isomorphism. -/
theorem model_suzuki_or_three_dvd (h : TheoremCModel K) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) ∨ 3 ∣ Nat.card K := by
  cases h with
  | alternating n hn iso =>
      right
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      obtain ⟨hnlo, hnhi⟩ := hn
      interval_cases n <;>
        simp only [Nat.card_eq_fintype_card, _root_.card_alternatingGroup] <;> norm_num
  | linear_odd p e hp ho he hs iso => exact Or.inr (linear (by decide) iso)
  | three_odd p hp ho unitary iso =>
      right
      cases unitary with
      | false => exact linear (by decide) iso
      | true =>
          obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := iso
          rw [Nat.card_congr e.toEquiv]
          exact unitary_prime_three_dvd J p hp hcard hconj
  | rank_one iso => exact bender iso
  | rank_two iso => exact Or.inr (rank_two iso)
  | binary_linear n hn iso =>
      exact Or.inr (linear (by rcases hn with rfl | rfl <;> decide) iso)
  | sporadic name hne iso =>
      right
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact sporadic_three_dvd name hne
  | janko_one iso =>
      right
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact Janko1.orderOf_b ▸ orderOf_dvd_natCard Janko1.b

/-- The three nonsimple alternatives in A.3.6 also have a three divisor:
    in the center for a cover, and in the actual SL₂ quotient otherwise. -/
theorem a36_suzuki_of_coprime {X : Type*} [Group X] [Finite X] {B : Subgroup X}
    (h : A36Conclusion B) (hthree : Nat.Coprime 3 (Nat.card B)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (B ≃* SuzukiMatrixGroup m) := by
  have hn := Nat.prime_three.coprime_iff_not_dvd.mp hthree
  cases h.1 with
  | simple hc hs hm => exact (model_suzuki_or_three_dvd hm).resolve_right hn
  | cover hc hz hm =>
      obtain ⟨e⟩ := hz
      have he : Nat.card (center B) = 3 := by
        rw [Nat.card_congr e.toEquiv]
        simp
      exact (hn (he ▸ (center B).card_subgroup_dvd_card)).elim
  | natural h =>
      obtain ⟨p, hp, hlarge, F, hF, hfin, hcard, v, ρ, haction⟩ := h.2
      have hd : 3 ∣ Nat.card (B ⧸ generalizedFitting B) := by
        rw [Nat.card_congr ρ.toEquiv]
        exact special_linear_two F
      exact (hn (hd.trans (generalizedFitting B).card_quotient_dvd_card)).elim
  | nilpotent h =>
      obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h.2.2.1
      have hd : 3 ∣ Nat.card (B ⧸ generalizedFitting B) := by
        rw [Nat.card_congr e.toEquiv]
        exact special_linear_two F
      exact (hn (hd.trans (generalizedFitting B).card_quotient_dvd_card)).elim

/-- The conditional catalogue deduction in 13.6.27, applied to the image
    in H/O₂(H), then transported through the genuine intrinsic quotient map. -/
theorem component_suzuki_quotient {H : Type u} [Group H] [Finite H]
    {κ : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (hQ : IsSQTK κ (H ⧸ pCore 2 H))
    {D : Subgroup H} (hD : D.IsCComponent) (hthree : Nat.Coprime 3 (Nat.card D)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m) := by
  let eQ := cComponentTwoCoreQuotientEquiv hD
  have hqthree : Nat.Coprime 3 (Nat.card (D.map (QuotientGroup.mk' (pCore 2 H)))) := by
    rw [← Nat.card_congr eQ.toEquiv]
    exact hthree.coprime_dvd_right (pCore 2 D).card_quotient_dvd_card
  obtain ⟨m, hm, ⟨e⟩⟩ := a36_suzuki_of_coprime
    (proposition_1_2_1_four_earlier_conclusion hA36 hQ hD) hqthree
  exact ⟨m, hm, ⟨eQ.trans e⟩⟩

/-- The literal quotient input to `SuzukiIsolation.hz_component_obstruction`.
    Here H is the ambient subgroup and D is its intrinsic C-component. -/
theorem hz_component_suzuki_quotient {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (H : Subgroup G) (hQ : IsSQTK κ (H ⧸ pCore 2 H))
    (D : Subgroup H) (hD : D.IsCComponent) (hthree : Nat.Coprime 3 (Nat.card D)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m) :=
  component_suzuki_quotient hA36 hQ hD hthree

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
