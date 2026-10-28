module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointCore
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Quaternion factors in the binary unitary point core

The literal Heisenberg radical has order 32 and center of order two.
The coordinate slice `y = 0` is a normal elementary subgroup of order eight,
so extraspecial recognition gives two commuting quaternion factors. The
scalar quotient of the full point stabilizer has order three; restriction
to the vector stabilizer therefore identifies its two-core with this same
radical. The actual projective map transports the factors to the stored
point parabolic, retaining the intrinsic two-core.

Source: Aschbacher--Smith, 13.5.17 and F.4.29, printed pp.920--922 and 289;
the Heisenberg coordinates are the unitary point model of F.1.12(I)(6).
This proves the concrete core input to the marked point comparison.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointQuaternion
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 (Nat.le_refl 1)
local notation "R" => PointLocal.Radical 1 (Nat.le_refl 1)
local notation "κ" => coordinatesOfRadical F σ hσ

private theorem coord_ext (a b : R) (hx : (κ a).x = (κ b).x)
    (hy : (κ a).y = (κ b).y) (hz : (κ a).z = (κ b).z) : a = b := by
  apply (radicalCoordinatesEquiv F σ hσ).symm.injective
  change κ a = κ b
  cases hca : κ a
  cases hcb : κ b
  simp_all

private theorem coord_mul (a b : R) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y ∧
    (κ (a*b)).z = (κ a).z + (κ b).z + σ (κ a).y * (κ b).x +
      σ (κ a).x * (κ b).y := by
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact radical_mul_coordinates F σ hσ c d

private def yHom : R →* Multiplicative F where
  toFun a := Multiplicative.ofAdd (κ a).y
  map_one' := rfl
  map_mul' a b := (coord_mul a b).2.1

private def eight : Subgroup R := yHom.ker
private instance : eight.Normal := MonoidHom.normal_ker _

private def eightEquiv : eight ≃ F × PointLocal.FixedField 1 where
  toFun a := ((κ a.val).x, ⟨(κ a.val).z, by
    have hy : (κ a.val).y = 0 := a.property
    have ht := (κ a.val).trace_eq
    rw [hy] at ht
    have hz : (κ a.val).z + σ (κ a.val).z = 0 := by simpa using ht
    exact (eq_neg_of_add_eq_zero_right hz).trans (CharTwo.neg_eq _)⟩)
  invFun a := ⟨radicalOfCoordinates F σ hσ ⟨a.1,0,a.2,by
    have ht : σ (a.2 : F) = a.2 := a.2.property
    simp [ht, CharTwo.add_self_eq_zero]⟩, rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply coord_ext
    · rfl
    · exact (show (κ a.val).y = 0 from a.property).symm
    · rfl
  right_inv a := by cases a; rfl

private theorem eight_card : Nat.card eight = 8 := by
  rw [Nat.card_congr eightEquiv, Nat.card_prod,
    matrixField_card 1 (Nat.le_refl 1), PointLocal.fixedField_card 1 (Nat.le_refl 1)]
  norm_num

private theorem elementary_of_square {G : Type*} [Group G]
    (hs : ∀ a : G, a ^ 2 = 1) : IsElementaryAbelian 2 G := by
  have hi (a : G) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs a)
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

private instance : IsElementaryAbelian 2 eight := by
  apply elementary_of_square
  intro a
  apply Subtype.ext
  change a.val ^ 2 = 1
  rw [pow_two]
  have hy : (κ a.val).y = 0 := a.property
  apply coord_ext
  · rw [(coord_mul _ _).1]
    exact CharTwo.add_self_eq_zero (κ a.val).x
  · rw [(coord_mul _ _).2.1]
    exact CharTwo.add_self_eq_zero (κ a.val).y
  · simp only [(coord_mul _ _).2.2, hy, map_zero, zero_mul, mul_zero,
      CharTwo.add_self_eq_zero]
    rfl

private theorem center_le_eight : center R ≤ eight := by
  intro a ha
  exact ((mem_center_radical_iff F σ hσ
    (PointLocal.fieldConj_nontrivial 1 (Nat.le_refl 1)) a).mp ha).2

private theorem radical_extraspecial : IsExtraspecial 2 R := by
  have hc : Nat.card (center R) = 2 := PointLocal.radical_center_card 1 (Nat.le_refl 1)
  have hr : Nat.card R = 32 := PointLocal.radical_card 1 (Nat.le_refl 1)
  have hq : Nat.card (R ⧸ center R) = 16 := by
    have h := (center R).card_mul_index
    rw [hc, hr, index_eq_card] at h
    omega
  refine {
    center_order_p := hc
    quotient_elementary_abelian := elementary_of_square ?_
    quotient_nontrivial := ?_ }
  · intro a
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (center R) a
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (radical_square_mem_center F σ hσ a)
  · classical
    let := Fintype.ofFinite (R ⧸ center R)
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card, hq]
    decide

/-- The actual vector-stabilizer radical is a central product of quaternion eights. -/
theorem radical_quaternion : Nonempty (QuaternionCentralProductData R) := by
  let : IsExtraspecial 2 R := radical_extraspecial
  obtain ⟨B,C,hB,hC,hgen,hi,hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary
      (show Nat.card R = 32 from PointLocal.radical_card 1 (Nat.le_refl 1))
      eight eight_card center_le_eight
  exact ⟨⟨B,C,hB,hC,hi,hcomm,hgen⟩⟩

local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "L" => localSU F (form F σ hσ)
local notation "Q" => UnitaryFourConverse.PointParabolic.parabolicRadical F σ hσ

/-- The Heisenberg radical is the two-core of the full line stabilizer. -/
theorem parabolic_radical_eq_core : Q = pCore 2 P := by
  apply le_antisymm (UnitaryFourConverse.PointParabolic.parabolicRadical_le_twoCore F σ hσ)
  let i : L →* P := Subgroup.inclusion (localSU_le_pointParabolicSU F _)
  have hi : Function.Injective i := Subgroup.inclusion_injective _
  let K : Subgroup L := (pCore 2 P).comap i
  have hK : K ≤ R := by
    change K ≤ radical F σ hσ
    rw [UnitaryFourPointQuotient.radical_eq_twoCore F σ hσ
      (PointLocal.radical_isTwoGroup 1 (Nat.le_refl 1))]
    exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  let f := UnitaryFourConverse.PointParabolic.scalarHom F σ hσ
  have hfcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, matrixField_card 1 (Nat.le_refl 1)]
    norm_num
  intro x hx
  have hscalar : f x = 1 := by
    obtain ⟨y,hy⟩ := (pCore_isPGroup.powEquiv (by decide : Nat.Coprime 2 3)).surjective
      (⟨x,hx⟩ : pCore 2 P)
    have hy' : (y : P) ^ 3 = x := congrArg Subtype.val hy
    rw [← hy', map_pow]
    simpa only [hfcard] using pow_card_eq_one' (x := f y.val)
  have hlocal : x.val ∈ L := by
    have hxk : x ∈ f.ker := hscalar
    rw [UnitaryFourConverse.PointParabolic.scalarHom_ker] at hxk
    exact hxk
  let z : L := ⟨x.val,hlocal⟩
  exact ⟨z,hK (show i z ∈ pCore 2 P from hx),rfl⟩

/-- The actual inclusion identifies the vector radical with its image in the line stabilizer. -/
def parabolicRadicalEquiv : R ≃* Q :=
  (radical F σ hσ).equivMapOfInjective
    (Subgroup.inclusion (localSU_le_pointParabolicSU F (form F σ hσ)))
    (Subgroup.inclusion_injective _)

/-- Quaternion factors in the intrinsic matrix point core. -/
def pointQuaternionData : QuaternionCentralProductData (pCore 2 P) :=
  (Classical.choice radical_quaternion).map
    (parabolicRadicalEquiv.trans (MulEquiv.subgroupCongr parabolic_radical_eq_core))

/-- Quaternion factors in the intrinsic point core of the literal projective model. -/
def projectivePointQuaternionData :
    QuaternionCentralProductData (pCore 2 (pointParabolic 1 (Nat.le_refl 1))) := by
  let e : P ≃* pointParabolic 1 (Nat.le_refl 1) :=
    (pointParabolicMatrix 1 (Nat.le_refl 1)).equivMapOfInjective
      (projection 1 (Nat.le_refl 1)) (projection_injective 1 (Nat.le_refl 1))
  exact pointQuaternionData.map
    ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e)))
end CFSG.Quasithin.ChapterF.UnitaryTwo.PointQuaternion
