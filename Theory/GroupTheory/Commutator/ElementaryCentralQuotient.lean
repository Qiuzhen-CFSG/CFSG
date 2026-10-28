module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.End

open scoped commutatorElement IsMulCommutative
open Subgroup

/-! The commutator pairing for a group with elementary central quotient. -/

namespace Subgroup

public theorem exists_elementary_central_quotient_commutator_pairing
    {G : Type*} [Group G] [Finite G]
    [IsElementaryAbelian 2 (center G)]
    [IsElementaryAbelian 2 (G ⧸ center G)]
    (htrans : ∀ x y : G, x ∈ center G → y ∈ center G → orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut G, a x = y) :
    ∃ b : (G ⧸ center G) →* ((G ⧸ center G) →* center G),
      (∀ x y : G, (b (QuotientGroup.mk' (center G) x)
        (QuotientGroup.mk' (center G) y) : G) = ⁅x,y⁆) ∧
      (∀ x, b x x = 1) ∧
      (∀ x, (∀ y, b x y = 1) → x = 1) ∧
      (∀ z₁ z₂ : center G, z₁ ≠ 1 → z₂ ≠ 1 →
        ∃ (v : MulAut (G ⧸ center G)) (w : MulAut (center G)),
          w z₁ = z₂ ∧ ∀ x y, b (v x) (v y) = w (b x y)) ∧
      (∀ a : MulAut G, ∃ (v : MulAut (G ⧸ center G)) (w : MulAut (center G)),
        (∀ x : G, QuotientGroup.mk' (center G) (a x) =
          v (QuotientGroup.mk' (center G) x)) ∧
        ∀ x y, b (v x) (v y) = w (b x y)) := by
  let Z := center G
  let Q := G ⧸ Z
  let W := Z
  have hclass : _root_.commutator G ≤ Z :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hc (x y : G) : ⁅x,y⁆ ∈ Z :=
    hclass (commutator_mem_commutator (mem_top x) (mem_top y))
  have hconj (g : G) (x y : G) :
      g * ⁅x,y⁆ * g⁻¹ = ⁅x,y⁆ := by
    rw [mem_center_iff.mp (hc x y) g, mul_assoc, mul_inv_cancel, mul_one]
  let c (x y : G) : W := ⟨⁅x,y⁆, hc x y⟩
  have c_right (x y z : G) : c x (y*z) = c x y * c x z := by
    apply Subtype.ext
    change ⁅x, y*z⁆ = ⁅x,y⁆ * ⁅x,z⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      ⁅x,y⁆ * y * ⁅x,z⁆ * y⁻¹ = ⁅x,y⁆ * (y * ⁅x,z⁆ * y⁻¹) := by group
      _ = ⁅x,y⁆ * ⁅x,z⁆ := by rw [hconj]
  have c_left (x y z : G) : c (x*y) z = c x z * c y z := by
    apply Subtype.ext
    change ⁅x*y, z⁆ = ⁅x,z⁆ * ⁅y,z⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    calc
      x * ⁅y,z⁆ * x⁻¹ * ⁅x,z⁆ = (x * ⁅y,z⁆ * x⁻¹) * ⁅x,z⁆ := by rw [mul_assoc]
      _ = ⁅y,z⁆ * ⁅x,z⁆ := by rw [hconj]
      _ = ⁅x,z⁆ * ⁅y,z⁆ := mem_center_iff.mp (hc x z) ⁅y,z⁆
  have c_center_left (z y : G) (hz : z ∈ Z) : c z y = 1 := by
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (mem_center_iff.mp hz y).symm
  have c_center_right (x z : G) (hz : z ∈ Z) : c x z = 1 := by
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact mem_center_iff.mp hz x
  let f (x : G) : G →* W :=
    { toFun := c x
      map_one' := c_center_right x 1 (one_mem Z)
      map_mul' := by intro y z; exact c_right x y z }
  have f_center (z : G) (hz : z ∈ Z) : f z = 1 := by
    apply MonoidHom.ext
    intro y
    exact c_center_left z y hz
  let g (x : G) : Q →* W :=
    QuotientGroup.lift Z (f x) (by
      intro z hz
      exact (MonoidHom.mem_ker).2 (by simpa [f] using c_center_right x z hz))
  have g_mul (x y : G) : g (x*y) = g x * g y := by
    apply MonoidHom.ext
    intro t
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Z t
    change c (x*y) z = c x z * c y z
    exact c_left x y z
  have g_center (z : G) (hz : z ∈ Z) : g z = 1 := by
    apply MonoidHom.ext
    intro t
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z t
    exact c_center_left z y hz
  let b : Q →* (Q →* W) :=
    QuotientGroup.lift Z
      { toFun := g
        map_one' := by
          apply MonoidHom.ext
          intro t
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z t
          exact c_center_left 1 y (one_mem Z)
        map_mul' := by intro x y; exact g_mul x y }
      (by
        intro z hz
        apply MonoidHom.mem_ker.mpr
        exact g_center z hz)
  have hb (x y : G) : (b (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y) : G) = ⁅x,y⁆ := by
    change (c x y : G) = ⁅x,y⁆
    rfl
  have hdiag (x : Q) : b x x = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
    apply Subtype.ext
    rw [hb]
    simp
  have hrad (x : Q) (hx : ∀ y, b x y = 1) : x = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
    apply (QuotientGroup.eq_one_iff g).2
    rw [mem_center_iff]
    intro y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hy := congrArg Subtype.val (hx (QuotientGroup.mk' Z y))
    rw [hb g y] at hy
    rw [← commutatorElement_inv, hy]
    simp
  have induced (a : MulAut G) :
      ∃ v : MulAut Q, ∃ w : MulAut W,
        w = Subgroup.centerCongr a ∧
        (∀ x : G, QuotientGroup.mk' Z (a x) = v (QuotientGroup.mk' Z x)) ∧
        ∀ x y, b (v x) (v y) = w (b x y) := by
    let hcA : Z.map a.toMonoidHom = Z :=
      (Subgroup.characteristic_iff_map_eq.mp centerCharacteristic a)
    let v : MulAut Q := QuotientGroup.congr Z Z a hcA
    let w : MulAut W := Subgroup.centerCongr a
    refine ⟨v, w, rfl, ?_, ?_⟩
    · intro x
      rfl
    · intro x y
      obtain ⟨gx, rfl⟩ := QuotientGroup.mk'_surjective Z x
      obtain ⟨gy, rfl⟩ := QuotientGroup.mk'_surjective Z y
      apply Subtype.ext
      change ⁅a gx, a gy⁆ = a ⁅gx,gy⁆
      simp [commutatorElement_def]
  have htranspair (z₁ z₂ : W) (hz₁ : z₁ ≠ 1) (hz₂ : z₂ ≠ 1) :
      ∃ (v : MulAut Q) (w : MulAut W), w z₁ = z₂ ∧
        ∀ x y, b (v x) (v y) = w (b x y) := by
    have ho1 : orderOf (z₁ : G) = 2 := by
      have hpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) (z₁ : G) z₁.property
      exact (orderOf_eq_prime hpow (by simpa using hz₁))
    have ho2 : orderOf (z₂ : G) = 2 := by
      have hpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) (z₂ : G) z₂.property
      exact (orderOf_eq_prime hpow (by simpa using hz₂))
    obtain ⟨a, ha⟩ := htrans z₁ z₂ z₁.property z₂.property ho1 ho2
    obtain ⟨v, w0, hw0, _, hw⟩ := induced a
    refine ⟨v, w0, ?_, hw⟩
    rw [hw0]
    apply Subtype.ext
    exact ha
  refine ⟨b, hb, hdiag, hrad, htranspair, ?_⟩
  intro a
  obtain ⟨v, w, _, hv, hw⟩ := induced a
  exact ⟨v, w, hv, hw⟩

end Subgroup
