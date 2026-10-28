module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ImageModels
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity

/-!
# Excluding PSU₅(4) using the full natural quotient

A nontrivial two-subgroup of the actual projective unitary group fixes an
isotropic line or plane. Its normalizer therefore lies in a conjugate full
parabolic. The original quotient L/O₂(L) divides the order of the residual
image, hence the parabolic order. Neither of the two certified parabolic
orders permits any nonbinary natural quotient. The proof retains the full
SL₃ center and needs no containment of a Sylow subgroup.

PlacedModels applies this to the selected component in the literal N_G(A);
Source carries it to the original elementary Hall kernel. The remaining
odd B-model and J₄/Ru exclusions stay with this task.
Source: Aschbacher--Smith 4.4.12, pp.621--622, and F.1.12(7), pp.263--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {Q : Type*} [Group Q] [Finite Q]
include D S

private theorem quotient_order_not_dvd_unitary_five_parabolic (n : ℕ)
    (hn : n = 2 ^ 20 * (3 ^ 2 * 5 ^ 2 * 13) ∨ n = 2 ^ 20 * (3 ^ 2 * 5 * 17)) :
    ¬ Nat.card (L ⧸ pCore 2 L) ∣ n := by
  intro hd
  have hnpos : 0 < n := by rcases hn with rfl | rfl <;> decide
  have hnb : n ≤ 3067084800 := by rcases hn with rfl | rfl <;> decide
  have hb := (Nat.le_of_dvd hnpos hd).trans hnb
  have hlo := S.nonbinary
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order] at hd hb
    have hf : S.field.degree ≤ 3 := by
      by_contra! hf
      have hq : 16 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
      norm_num at hl
      omega
    rcases hn with rfl | rfl <;> interval_cases hh : S.field.degree <;>
      norm_num [S.field.card_eq,hh] at hd
  | sp4 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hd hb
    have hf : S.field.degree ≤ 3 := by
      by_contra! hf
      have hq : 16 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
      norm_num at hl
      omega
    rcases hn with rfl | rfl <;> interval_cases hh : S.field.degree <;>
      norm_num [S.field.card_eq,hh] at hd
  | g2 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,Atlas.G2.card_Model] at hd hb
    have hf : S.field.degree ≤ 3 := by
      by_contra! hf
      have hq : 16 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
      norm_num at hl
      omega
    rcases hn with rfl | rfl <;> interval_cases hh : S.field.degree <;>
      norm_num [S.field.card_eq,hh] at hd

/-- The literal two-local image of the original covering residual excludes PSU₅(4). -/
theorem NaturalCoverImage.not_unitary_five_four (h : NaturalCoverImage D Q)
    (hm : ClassicalGroup.IsPSU Q 5 4) : False := by
  classical
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := projective_equiv_identity_four J hcard hconj
  let J' := HermitianForm.IdentityGram.identityGram J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J') := finite_projective J'
  obtain ⟨X,U,hX,hU,hUX,hN,hcardU,⟨eq⟩⟩ := h.of_equiv D (e.trans a)
  have hsize : 64 ≤ Nat.card U := Nat.le_of_dvd (Nat.card_pos (α := U))
    ((natural_two_parts D S).1.trans hcardU)
  have hne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hsize; omega
  let M := normalizer (U : Set (ProjectiveSpecialUnitaryMatrixGroup J'))
  have hM : IsTwoLocal M := ⟨U,hne,hU.isPGroup,rfl⟩
  obtain ⟨W,hn,hi,_,hMW⟩ := IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
    J' rfl M hM
  obtain ⟨b,g,hg⟩ := IsotropicTransitivity.transitive J' hcard hconj rfl W hn hi
  have he : parabolic J' W = (if b then planeParabolic J' else lineParabolic J').map
      (MulAut.conj (project J' g)).toMonoidHom := by
    rw [hg,IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hMW
  let j := (MulAut.conj (project J' g)⁻¹).toMonoidHom.comp X.subtype
  have hj : Function.Injective j := (MulAut.conj (project J' g)⁻¹).injective.comp
    X.subtype_injective
  have hc : j.range ≤ (if b then planeParabolic J' else lineParabolic J') := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,hey⟩ := hMW (hN x.property)
    change (project J' g)⁻¹ * (x : ProjectiveSpecialUnitaryMatrixGroup J') *
      ((project J' g)⁻¹)⁻¹ ∈ _
    rw [←hey]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  have hdX : Nat.card (L ⧸ pCore 2 L) ∣ Nat.card X := by
    rw [← Nat.card_congr eq.toEquiv]
    exact card_quotient_dvd_card (pCore 2 X)
  have hd : Nat.card (L ⧸ pCore 2 L) ∣
      Nat.card ↥(if b then planeParabolic J' else lineParabolic J') := by
    apply hdX.trans
    rw [Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
    exact card_dvd_of_le hc
  cases b
  · change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (lineParabolic J') at hd
    rw [card_lineParabolic_four J' hcard hconj rfl] at hd
    exact quotient_order_not_dvd_unitary_five_parabolic D S _ (Or.inl rfl) hd
  · change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (planeParabolic J') at hd
    rw [card_planeParabolic_four J' hcard hconj rfl] at hd
    exact quotient_order_not_dvd_unitary_five_parabolic D S _ (Or.inr rfl) hd
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
