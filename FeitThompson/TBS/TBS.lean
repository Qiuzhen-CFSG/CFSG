module

public import FeitThompson.Gorenstein.Chapter8_2

/-!
# Huppert--Blackburn X.1.12, Thompson--Bender

This file records the Lean-facing statement of the Thompson--Bender theorem
from Huppert--Blackburn, Vol. III, Chapter X, Theorem 1.12.

The expanded proof route lives in
`FeitThompson/TBS/full-proof/thompson_bender_signalizer_lemma.tex`, and the
Lean-oriented decomposition lives in
`FeitThompson/TBS/step-proof/thompson_bender_signalizer_lemma/`.
-/

open scoped Pointwise commutatorElement IsMulCommutative

universe u


/-- Baer's odd class-two abelian model: same elements, twisted multiplication. -/
public structure TBSBaer (r : ℕ) (G : Type u) where
  val : G

namespace TBSBaer

public instance {r : ℕ} {G : Type u} : CoeOut (TBSBaer r G) G where
  coe x := x.val

@[simp] public theorem ext_iff {r : ℕ} {G : Type u} {x y : TBSBaer r G} :
    x = y ↔ x.val = y.val := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases x
    cases y
    simp at h
    simp [h]

@[expose]
public def mul {r : ℕ} {G : Type u} [Group G] (x y : TBSBaer r G) : TBSBaer r G :=
  ⟨x.val * y.val * ⁅y.val, x.val⁆ ^ r⟩

@[expose]
public def one {r : ℕ} {G : Type u} [One G] : TBSBaer r G := ⟨1⟩

@[expose]
public def inv {r : ℕ} {G : Type u} [Inv G] (x : TBSBaer r G) : TBSBaer r G := ⟨x.val⁻¹⟩

public instance {r : ℕ} {G : Type u} [Group G] : Mul (TBSBaer r G) where
  mul := TBSBaer.mul

public instance {r : ℕ} {G : Type u} [One G] : One (TBSBaer r G) where
  one := TBSBaer.one

public instance {r : ℕ} {G : Type u} [Inv G] : Inv (TBSBaer r G) where
  inv := TBSBaer.inv

@[simp] public theorem coe_mul {r : ℕ} {G : Type u} [Group G] (x y : TBSBaer r G) :
    ((x * y : TBSBaer r G) : G) = (x : G) * (y : G) * ⁅(y : G), (x : G)⁆ ^ r := rfl

@[simp] public theorem coe_one {r : ℕ} {G : Type u} [One G] :
    ((1 : TBSBaer r G) : G) = (1 : G) := rfl

@[simp] public theorem coe_inv {r : ℕ} {G : Type u} [Inv G] (x : TBSBaer r G) :
    ((x⁻¹ : TBSBaer r G) : G) = ((x : G)⁻¹ : G) := rfl

public theorem commutator_mem_center_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  exact hcomm <|
    Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
      (show x ∈ (⊤ : Subgroup G) by trivial) (show y ∈ (⊤ : Subgroup G) by trivial)

public theorem swap_mul_commutator_of_mem_center {G : Type u} [Group G] {x y : G}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := (Subgroup.mem_center_iff.mp hcomm) x
  have hy : y * ⁅y, x⁆ = ⁅y, x⁆ * y := (Subgroup.mem_center_iff.mp hcomm) y
  calc
    y * x = ⁅y, x⁆ * x * y := by
      simp [commutatorElement_def, mul_assoc]
    _ = x * ⁅y, x⁆ * y := by
      rw [← hx, mul_assoc]
    _ = x * (⁅y, x⁆ * y) := by
      simp [mul_assoc]
    _ = x * (y * ⁅y, x⁆) := by
      rw [← hy]
    _ = x * y * ⁅y, x⁆ := by
      simp [mul_assoc]

public theorem commutator_mul_right_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hzcent : ⁅x, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm x z
  have hzy : y * ⁅x, z⁆ = ⁅x, z⁆ * y :=
    (Subgroup.mem_center_iff.mp hzcent y)
  calc
    ⁅x, y * z⁆ = ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ := by
      rw [commutator_mul_right]
    _ = ⁅x, y⁆ * (y * ⁅x, z⁆) * y⁻¹ := by simp [mul_assoc]
    _ = ⁅x, y⁆ * (⁅x, z⁆ * y) * y⁻¹ := by rw [hzy]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by simp [mul_assoc]

public theorem commutator_mul_left_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hycent : ⁅y, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y z
  have hxcent : ⁅x, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm x z
  have hxy : x * ⁅y, z⁆ = ⁅y, z⁆ * x :=
    (Subgroup.mem_center_iff.mp hycent x)
  have hyx : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    (Subgroup.mem_center_iff.mp hycent ⁅x, z⁆).symm
  calc
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      rw [commutator_mul_left]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by
      rw [hxy]
      simp [mul_assoc]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hyx

public theorem commutator_eq_one_of_right_mem_center
    {G : Type u} [Group G] {x z : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, z⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz x))

public theorem commutator_eq_one_of_left_mem_center
    {G : Type u} [Group G] {z x : G} (hz : z ∈ Subgroup.center G) :
    ⁅z, x⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz x).symm)

public theorem commutator_right_baer_factor
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y * ⁅y, x⁆ ^ r⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  let c : G := ⁅y, x⁆
  have hc : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y x
  have hcpow : c ^ r ∈ Subgroup.center G := (Subgroup.center G).pow_mem hc r
  calc
    ⁅z, x * y * c ^ r⁆ = ⁅z, x * y⁆ * ⁅z, c ^ r⁆ := by
      rw [commutator_mul_right_of_commutator_le_center hcomm]
    _ = ⁅z, x * y⁆ := by
      rw [commutator_eq_one_of_right_mem_center hcpow]
      simp
    _ = ⁅z, x⁆ * ⁅z, y⁆ := by
      rw [commutator_mul_right_of_commutator_le_center hcomm]

public theorem commutator_left_baer_factor
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅y * z * ⁅z, y⁆ ^ r, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
  let c : G := ⁅z, y⁆
  have hc : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm z y
  have hcpow : c ^ r ∈ Subgroup.center G := (Subgroup.center G).pow_mem hc r
  calc
    ⁅y * z * c ^ r, x⁆ = ⁅y * z, x⁆ * ⁅c ^ r, x⁆ := by
      rw [commutator_mul_left_of_commutator_le_center hcomm]
    _ = ⁅y * z, x⁆ := by
      rw [commutator_eq_one_of_left_mem_center hcpow]
      simp
    _ = ⁅y, x⁆ * ⁅z, x⁆ := by
      rw [commutator_mul_left_of_commutator_le_center hcomm]

public theorem center_three_mul_rotate {G : Type u} [Group G] {a b c : G}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G)
    (hc : c ∈ Subgroup.center G) :
    a * (b * c) = c * (a * b) := by
  let aZ : Subgroup.center G := ⟨a, ha⟩
  let bZ : Subgroup.center G := ⟨b, hb⟩
  let cZ : Subgroup.center G := ⟨c, hc⟩
  have h : aZ * (bZ * cZ) = cZ * (aZ * bZ) := by
    simp [mul_assoc, mul_comm]
  exact congrArg Subtype.val h

public theorem mul_assoc_of_commutator_le_center
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (x y z : TBSBaer r G) :
    (x * y) * z = x * (y * z) := by
  apply (ext_iff (G := G)).2
  let a : G := x.val
  let b : G := y.val
  let c : G := z.val
  let cba : G := ⁅b, a⁆
  let cca : G := ⁅c, a⁆
  let ccb : G := ⁅c, b⁆
  have hcba : cba ^ r ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem
      (commutator_mem_center_of_commutator_le_center hcomm b a) r
  have hcca : cca ^ r ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem
      (commutator_mem_center_of_commutator_le_center hcomm c a) r
  have hccb : ccb ^ r ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem
      (commutator_mem_center_of_commutator_le_center hcomm c b) r
  have hpow_zxzy :
      (cca * ccb) ^ r = cca ^ r * ccb ^ r := by
    exact (show Commute cca ccb from
      Subgroup.mem_center_iff.mp
        (commutator_mem_center_of_commutator_le_center hcomm c a) ccb |>.symm).mul_pow r
  have hpow_yxzx :
      (cba * cca) ^ r = cba ^ r * cca ^ r := by
    exact (show Commute cba cca from
      Subgroup.mem_center_iff.mp
        (commutator_mem_center_of_commutator_le_center hcomm b a) cca |>.symm).mul_pow r
  have hleft :
      (((x * y) * z : TBSBaer r G) : G) =
        a * b * c * (cba ^ r * (cca ^ r * ccb ^ r)) := by
    calc
      (((x * y) * z : TBSBaer r G) : G)
          = (a * b * cba ^ r) * c *
              ⁅c, a * b * cba ^ r⁆ ^ r := rfl
      _ = (a * b * cba ^ r) * c * (cca * ccb) ^ r := by
        rw [commutator_right_baer_factor (r := r) hcomm a b c]
      _ = (a * b * cba ^ r) * c * (cca ^ r * ccb ^ r) := by
        rw [hpow_zxzy]
      _ = a * b * c * (cba ^ r * (cca ^ r * ccb ^ r)) := by
        have hmove : cba ^ r * c = c * cba ^ r :=
          (Subgroup.mem_center_iff.mp hcba c).symm
        rw [show (a * b * cba ^ r) * c = a * b * c * cba ^ r by
          calc
            (a * b * cba ^ r) * c = a * b * (cba ^ r * c) := by simp [mul_assoc]
            _ = a * b * (c * cba ^ r) := by rw [hmove]
            _ = a * b * c * cba ^ r := by simp [mul_assoc]]
        simp [mul_assoc]
  have hright :
      ((x * (y * z) : TBSBaer r G) : G) =
        a * b * c * (ccb ^ r * (cba ^ r * cca ^ r)) := by
    calc
      ((x * (y * z) : TBSBaer r G) : G)
          = a * (b * c * ccb ^ r) *
              ⁅b * c * ccb ^ r, a⁆ ^ r := rfl
      _ = a * (b * c * ccb ^ r) * (cba * cca) ^ r := by
        rw [commutator_left_baer_factor (r := r) hcomm a b c]
      _ = a * (b * c * ccb ^ r) * (cba ^ r * cca ^ r) := by
        rw [hpow_yxzx]
      _ = a * b * c * (ccb ^ r * (cba ^ r * cca ^ r)) := by
        simp [mul_assoc]
  rw [hleft, hright]
  congr 1
  exact center_three_mul_rotate hcba hcca hccb

public theorem one_mul {G : Type u} [Group G] {r : ℕ} (x : TBSBaer r G) :
    (1 : TBSBaer r G) * x = x := by
  apply (ext_iff (G := G)).2
  simp

public theorem mul_one {G : Type u} [Group G] {r : ℕ} (x : TBSBaer r G) :
    x * (1 : TBSBaer r G) = x := by
  apply (ext_iff (G := G)).2
  simp

public theorem inv_mul_cancel {G : Type u} [Group G] {r : ℕ} (x : TBSBaer r G) :
    x⁻¹ * x = (1 : TBSBaer r G) := by
  apply (ext_iff (G := G)).2
  simp [commutatorElement_def]

@[reducible]
public def group {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) : Group (TBSBaer r G) where
  mul := (· * ·)
  mul_assoc := TBSBaer.mul_assoc_of_commutator_le_center hcomm
  one := 1
  one_mul := TBSBaer.one_mul
  mul_one := TBSBaer.mul_one
  inv := Inv.inv
  div := fun x y => x * y⁻¹
  div_eq_mul_inv := by intros; rfl
  zpow := zpowRec
  zpow_zero' := by intros; rfl
  zpow_succ' := by intros; rfl
  zpow_neg' := by intros; rfl
  inv_mul_cancel := TBSBaer.inv_mul_cancel

public def equiv {G : Type u} {r : ℕ} : TBSBaer r G ≃ G where
  toFun x := x.val
  invFun g := ⟨g⟩
  left_inv x := by cases x; rfl
  right_inv g := rfl

public instance finite {G : Type u} [Finite G] {r : ℕ} : Finite (TBSBaer r G) :=
  Finite.of_equiv G (equiv (G := G) (r := r)).symm

public theorem smul_commutatorElement
    {A G : Type u} [Group A] [Group G] [MulDistribMulAction A G]
    (a : A) (x y : G) :
    a • ⁅x, y⁆ = ⁅a • x, a • y⁆ := by
  simp [commutatorElement_def]

@[reducible]
public def action {A G : Type u} [Group A] [Group G] [MulDistribMulAction A G]
    {r : ℕ} (hcomm : _root_.commutator G ≤ Subgroup.center G) :
    letI : Group (TBSBaer r G) := group hcomm
    MulDistribMulAction A (TBSBaer r G) := by
  letI : Group (TBSBaer r G) := group hcomm
  exact {
    smul a x := ⟨a • x.val⟩
    one_smul x := by
      apply (ext_iff (G := G)).2
      change (1 : A) • x.val = x.val
      simp
    mul_smul a b x := by
      apply (ext_iff (G := G)).2
      change (a * b) • x.val = a • b • x.val
      simp [mul_smul]
    smul_mul a x y := by
      apply (ext_iff (G := G)).2
      change
        a • (x.val * y.val * ⁅y.val, x.val⁆ ^ r) =
          (a • x.val) * (a • y.val) * ⁅a • y.val, a • x.val⁆ ^ r
      simp [smul_commutatorElement]
    smul_one a := by
      apply (ext_iff (G := G)).2
      change a • (1 : G) = 1
      simp }

public theorem pow_two_mul_half_eq_self_of_pow_prime_eq_one
    {G : Type u} [Group G] {p r : ℕ}
    {c : G} (hc : c ^ p = 1) (hhalf : 2 * r = p + 1) :
    c ^ (2 * r) = c := by
  rw [hhalf, pow_succ, hc]
  simp

public theorem mul_comm
    {G : Type u} [Group G] {p r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hpow : ∀ x : G, x ^ p = 1) (hhalf : 2 * r = p + 1)
    (x y : TBSBaer r G) :
    x * y = y * x := by
  apply (ext_iff (G := G)).2
  let c : G := ⁅y.val, x.val⁆
  have hc_cent : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y.val x.val
  have hc_pow : c ^ (2 * r) = c :=
    pow_two_mul_half_eq_self_of_pow_prime_eq_one (p := p) (r := r) (c := c) (hpow c) hhalf
  have hc_split : c = c ^ r * c ^ r := by
    simpa [pow_add, two_mul] using hc_pow.symm
  have hcomm_inv : ⁅x.val, y.val⁆ = c⁻¹ := by
    simp [c]
  have hcorr : c * c⁻¹ ^ r = c ^ r := by
    calc
      c * c⁻¹ ^ r = (c ^ r * c ^ r) * c⁻¹ ^ r := by
        exact congrArg (fun t : G => t * c⁻¹ ^ r) hc_split
      _ = c ^ r * (c ^ r * c⁻¹ ^ r) := by simp [mul_assoc]
      _ = c ^ r := by simp [inv_pow]
  calc
    ((x * y : TBSBaer r G) : G) = x.val * y.val * c ^ r := rfl
    _ = x.val * y.val * (c * c⁻¹ ^ r) := by
      rw [hcorr]
    _ = (x.val * y.val * c) * c⁻¹ ^ r := by simp [mul_assoc]
    _ = (y.val * x.val) * c⁻¹ ^ r := by
      rw [show y.val * x.val = x.val * y.val * c by
        simpa [c] using (TBSBaer.swap_mul_commutator_of_mem_center
          (x := x.val) (y := y.val) hc_cent)]
    _ = ((y * x : TBSBaer r G) : G) := by simp [hcomm_inv]

public theorem isMulCommutative
    {G : Type u} [Group G] {p r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hpow : ∀ x : G, x ^ p = 1) (hhalf : 2 * r = p + 1) :
    letI : Group (TBSBaer r G) := group hcomm
    IsMulCommutative (TBSBaer r G) := by
  letI : Group (TBSBaer r G) := group hcomm
  exact ⟨⟨fun x y => TBSBaer.mul_comm hcomm hpow hhalf x y⟩⟩

public theorem isPGroup
    {G : Type u} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hG : IsPGroup p G) :
    letI : Group (TBSBaer r G) := group hcomm
    IsPGroup p (TBSBaer r G) := by
  letI : Group (TBSBaer r G) := group hcomm
  obtain ⟨n, hcard⟩ := hG.exists_card_eq
  exact IsPGroup.of_card (p := p) (G := TBSBaer r G) (n := n) (by
    simpa [Nat.card_congr (equiv (G := G) (r := r))] using hcard)

end TBSBaer


