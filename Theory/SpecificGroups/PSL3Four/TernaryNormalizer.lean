module
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# A Frobenius nine-by-eight subgroup of the actual PSL₃(4)

The diagonal cubic and coordinate three-cycle commute projectively and
embed an elementary group of order nine. Two Fourier matrices embed Q₈
in SL₃(4). Their projective images normalize the nine, and every nonidentity
quaternion element acts without nonidentity fixed points on it. All finite
identities are checked by the kernel in the four-element quadratic field;
the quotient is the genuine scalar-center quotient of SL₃.

The representation consumer is PSL3Four.InvolutionDisplacement: the eight
weight translates give displacement at least four for the marked involution.
Its Chapter 12 application excludes the pure residual opposite-image branch
in Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.TernaryNormalizer
abbrev Four := QuadraticAlgebra (ZMod 2) 1 1
instance : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩
instance : Fintype Four := Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm
private abbrev E9 := Multiplicative (ZMod 3 × ZMod 3)
private abbrev Q8 := QuaternionGroup 2
private def w : Four := ⟨0,1⟩
private def first : SL(3,Four) := ⟨!![1,1,1;1,w,w^2;1,w^2,w],by decide +kernel⟩
private def second : SL(3,Four) := ⟨!![1,w^2,w^2;w,w,w^2;w,w^2,w],by decide +kernel⟩
private def diagonal : SL(3,Four) := ⟨!![1,0,0;0,w,0;0,0,w^2],by decide +kernel⟩
private def cycle : SL(3,Four) := ⟨!![0,1,0;0,0,1;1,0,0],by decide +kernel⟩
private def qword : Q8 → SL(3,Four)
  | .a n => first ^ n.val
  | .xa n => second * first ^ n.val

private theorem qword_mul : ∀ x y : Q8, qword (x*y) = qword x * qword y := by decide +kernel

private def qhom : Q8 →* SL(3,Four) where
  toFun := qword
  map_one' := by decide +kernel
  map_mul' := qword_mul

private def eword (x : E9) : SL(3,Four) := diagonal ^ x.toAdd.1.val * cycle ^ x.toAdd.2.val

private def scalar (i : Fin 3) : SL(3,Four) :=
  ⟨Matrix.scalar (Fin 3) (w ^ i.val),by fin_cases i <;> decide +kernel⟩

private theorem scalar_mem_center (i : Fin 3) : scalar i ∈ center SL(3,Four) := by
  apply SpecialLinearGroup.mem_center_iff.mpr
  let u : Fourˣ := ⟨w,w^2,by decide +kernel,by decide +kernel⟩
  exact ⟨u ^ i.val,by fin_cases i <;> decide +kernel,rfl⟩

private theorem eword_mul : ∀ x y : E9, ∃ i : Fin 3,
    eword (x*y) = scalar i * (eword x * eword y) := by decide +kernel

private theorem scalar_coverage : ∀ u : Four, u ^ 3 = 1 → ∃ i : Fin 3, u = w ^ i.val := by
  decide +kernel

private noncomputable def q : SL(3,Four) →* PSL(3,Four) := QuotientGroup.mk' (center _)

private theorem projective_eq_iff (x y : SL(3,Four)) : q x = q y ↔
    ∃ i : Fin 3, x = scalar i * y := by
  constructor
  · intro he
    obtain ⟨u,hu3,hu⟩ := SpecialLinearGroup.mem_center_iff.mp (QuotientGroup.eq_iff_div_mem.mp he)
    obtain ⟨i,hi⟩ := scalar_coverage u hu3
    refine ⟨i,?_⟩
    have hxy : x / y = scalar i := Subtype.ext (by rw [←hu]; exact congrArg (Matrix.scalar (Fin 3)) hi)
    exact (div_eq_iff_eq_mul).mp hxy
  · rintro ⟨i,rfl⟩
    rw [map_mul,show q (scalar i) = 1 from (QuotientGroup.eq_one_iff _).mpr (scalar_mem_center i),one_mul]

private noncomputable def ehom : E9 →* PSL(3,Four) where
  toFun x := q (eword x)
  map_one' := by rw [show eword 1 = 1 by decide +kernel,map_one]
  map_mul' x y := by
    rw [←map_mul]
    exact projective_eq_iff _ _ |>.mpr (eword_mul x y)

private noncomputable def phom : Q8 →* PSL(3,Four) := q.comp qhom

private theorem ehom_injective : Function.Injective ehom := by
  have h : ∀ x y : E9, ∀ i : Fin 3, eword x = scalar i * eword y → x = y := by decide +kernel
  intro x y he
  obtain ⟨i,hi⟩ := (projective_eq_iff _ _).mp he
  exact h x y i hi

private theorem phom_injective : Function.Injective phom := by
  have h : ∀ x y : Q8, ∀ i : Fin 3, qword x = scalar i * qword y → x = y := by decide +kernel
  intro x y he
  obtain ⟨i,hi⟩ := (projective_eq_iff _ _).mp he
  exact h x y i hi

private theorem normalizing_words : ∀ a : Q8, ∀ x : E9, ∃ y : E9, ∃ i : Fin 3,
    qword a * eword x = scalar i * (eword y * qword a) := by decide +kernel

private theorem free_words : ∀ a : Q8, ∀ x : E9, ∀ i : Fin 3, a ≠ 1 →
    qword a * eword x = scalar i * (eword x * qword a) → x = 1 := by decide +kernel

noncomputable def nine : Subgroup PSL(3,Four) := ehom.range
noncomputable def quaternion : Subgroup PSL(3,Four) := phom.range

instance nine_commutative : IsMulCommutative nine := by
  dsimp [nine]
  exact Subgroup.range_isMulCommutative ehom

theorem card_nine : Nat.card nine = 9 := by
  rw [nine,←Nat.card_congr (MonoidHom.ofInjective ehom_injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_quaternion : Nat.card quaternion = 8 := by
  rw [quaternion,←Nat.card_congr (MonoidHom.ofInjective phom_injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide

theorem quaternion_normalizes : quaternion ≤ normalizer (nine : Set PSL(3,Four)) := by
  intro a ha
  apply mem_normalizer_fintype
  intro x hx
  obtain ⟨b,rfl⟩ := ha
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨z,i,he⟩ := normalizing_words b y
  have hm : phom b * ehom y = ehom z * phom b := by
    change q (qword b) * q (eword y) = q (eword z) * q (qword b)
    rw [←map_mul,←map_mul]
    exact (projective_eq_iff _ _).mpr ⟨i,he⟩
  refine ⟨z,?_⟩
  rw [hm,mul_inv_cancel_right]

theorem quaternion_free (a : quaternion) (ha : a ≠ 1) (x : nine)
    (he : (a : PSL(3,Four)) * x * (a : PSL(3,Four))⁻¹ = x) : x = 1 := by
  obtain ⟨b,hb⟩ := a.property
  obtain ⟨y,hy⟩ := x.property
  have hn : b ≠ 1 := by
    intro h
    apply ha
    apply Subtype.ext
    rw [←hb,h,map_one]
    rfl
  have hm : q (qword b * eword y) = q (eword y * qword b) := by
    rw [map_mul,map_mul]
    change phom b * ehom y = ehom y * phom b
    rw [hb,hy]
    exact mul_inv_eq_iff_eq_mul.mp he
  obtain ⟨i,hi⟩ := (projective_eq_iff _ _).mp hm
  have hy1 := free_words b y i hn hi
  apply Subtype.ext
  rw [←hy,hy1,map_one]
  rfl

noncomputable def involution : quaternion :=
  ⟨phom (QuaternionGroup.a 2),⟨_,rfl⟩⟩

theorem involution_order : orderOf involution = 2 := by
  have hi := (MonoidHom.ofInjective phom_injective).orderOf_eq (QuaternionGroup.a 2)
  exact hi.trans (by rw [QuaternionGroup.orderOf_a]; decide)

end Matrix.PSL3Four.TernaryNormalizer
