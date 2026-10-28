module
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Three involutions with a central four-group of commutators

Three involutions whose pairwise commutators are the three nonidentity
elements of a central four-group generate a group of order thirty-two.
The first pair generates a dihedral group of order eight. An independent
central commutator doubles it, and the third involution doubles it again.

This is the elementary local calculation in Goldschmidt,
*Automorphisms of trivalent graphs* (1980), (6.12), printed p.405.
-/

public section
open Subgroup
open scoped commutatorElement
namespace ThreeInvolutionFourCommutators
variable {G : Type*} [Group G]

private theorem dihedral_centralizer_pair : ∀ x y v : DihedralGroup 4,
    x ^ 2 = 1 → y ^ 2 = 1 → ⁅x,y⁆ ≠ 1 →
      Commute v x → Commute v y → v = 1 ∨ v = ⁅x,y⁆ := by
  unfold Commute SemiconjBy
  decide

private theorem involution_normalizes_closure {t : G} (ht : t ^ 2 = 1)
    (S : Set G) (hc : ∀ x ∈ S, t * x * t⁻¹ ∈ closure S) :
    t ∈ normalizer (closure S : Set G) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have hh : (closure S).map (MulAut.conj t).toMonoidHom ≤ closure S := by
    rw [MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hh (mem_map.mpr ⟨x, hx, rfl⟩)
  · intro hx
    have hxx := hh (mem_map.mpr ⟨t * x * t⁻¹, hx, rfl⟩)
    change t * (t * x * t⁻¹) * t⁻¹ ∈ closure S at hxx
    have he : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [hti]
      calc
        t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [show t * t = 1 by simpa only [pow_two] using ht]; simp
    exact he ▸ hxx

/-- The order-thirty-two special two-group arising from three independent
involutions with the prescribed central four-group of commutators. -/
theorem card_closure_eq_thirty_two (x y z a b : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hz : z ^ 2 = 1)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b)
    (hxy : ⁅x,y⁆ = a) (hxz : ⁅x,z⁆ = b) (hyz : ⁅y,z⁆ = a*b)
    (hbx : Commute b x) (hby : Commute b y) (hbz : Commute b z) :
    Nat.card (closure ({x,y,z} : Set G)) = 32 := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy)
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hane : a ≠ 1 := by intro he; simp [he] at ha
  have hbne : b ≠ 1 := by intro he; simp [he] at hb
  let r := x * y
  have hr2 : r ^ 2 = a := by
    simpa only [commutatorElement_def, hxi, hyi, pow_two, mul_assoc, r] using hxy
  have hr : orderOf r = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hr2] using hane
    · simpa only [show 2^(1+1)=2*2 by decide, pow_mul, hr2] using ha2
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    dsimp [r]
    rw [mul_inv_rev, hyi, ← mul_assoc, ← pow_two, hx, one_mul]
  have hxout : x ∉ zpowers r := by
    rintro ⟨k, he⟩
    have hec : Commute x r := he ▸ (Commute.refl r).zpow_left k
    have hri : r⁻¹ = r := hxr.symm.trans (by rw [hec.eq, mul_inv_cancel_right])
    have hs : r ^ 2 = 1 := by
      calc
        r ^ 2 = r⁻¹ * r := by rw [pow_two, hri]
        _ = 1 := inv_mul_cancel r
    exact hane (hr2.symm.trans hs)
  obtain ⟨hH, ⟨eH⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion
    (by decide : 0 < 4) r x hr hx hxout hxr
  let H := zpowers r ⊔ zpowers x
  have hxH : x ∈ H := mem_sup_right (mem_zpowers x)
  have hrH : r ∈ H := mem_sup_left (mem_zpowers r)
  have hyH : y ∈ H := by
    have hh := H.mul_mem (H.inv_mem hxH) hrH
    simpa only [r, inv_mul_cancel_left] using hh
  have haH : a ∈ H := hr2 ▸ H.pow_mem hrH 2
  have hpair : H = closure ({x,y} : Set G) := by
    apply le_antisymm
    · exact sup_le
        (zpowers_le.mpr (mul_mem (subset_closure (by simp)) (subset_closure (by simp))))
        (zpowers_le.mpr (subset_closure (by simp)))
    · exact (closure_le _).mpr (by rintro w (rfl | rfl); exact hxH; exact hyH)
  have hbout : b ∉ H := by
    intro hbH
    let xx : H := ⟨x,hxH⟩
    let yy : H := ⟨y,hyH⟩
    let bb : H := ⟨b,hbH⟩
    have ha' : ⁅eH xx,eH yy⁆ ≠ 1 := by
      intro he
      have hh : ⁅xx,yy⁆ = (1 : H) := eH.injective (by
        rw [map_commutatorElement, map_one]; exact he)
      exact hane (hxy.symm.trans (congrArg Subtype.val hh))
    have hcases := dihedral_centralizer_pair (eH xx) (eH yy) (eH bb)
      (by rw [← map_pow, show xx ^ 2 = 1 from Subtype.ext hx, map_one])
      (by rw [← map_pow, show yy ^ 2 = 1 from Subtype.ext hy, map_one]) ha'
      ((show Commute bb xx from Subtype.ext hbx.eq).map eH.toMonoidHom)
      ((show Commute bb yy from Subtype.ext hby.eq).map eH.toMonoidHom)
    rcases hcases with he | he
    · have he' : bb = (1 : H) := eH.injective (by rw [map_one]; exact he)
      exact hbne (congrArg Subtype.val he')
    · have he' : bb = ⁅xx,yy⁆ := eH.injective (by rwa [map_commutatorElement])
      exact hne (hxy.symm.trans (congrArg Subtype.val he').symm)
  have hbN : b ∈ normalizer H := by
    rw [hpair]
    apply involution_normalizes_closure hb2
    rintro w (rfl | rfl)
    · rw [hbx.eq, mul_inv_cancel_right]
      exact subset_closure (by simp)
    · rw [hby.eq, mul_inv_cancel_right]
      exact subset_closure (by simp)
  let K := H ⊔ zpowers b
  have hK : Nat.card K = 16 := by
    change Nat.card (H ⊔ zpowers b : Subgroup G) = 16
    rw [card_sup_zpowers_of_normalizing_involution H b hb2 hbout hbN, hH]
  have hHN : K ≤ normalizer H := sup_le H.le_normalizer (zpowers_le.mpr hbN)
  have hxK : x ∈ K := mem_sup_left hxH
  have hyK : y ∈ K := mem_sup_left hyH
  have haK : a ∈ K := mem_sup_left haH
  have hbK : b ∈ K := mem_sup_right (mem_zpowers b)
  have hzout : z ∉ K := by
    intro hzK
    have hm := le_normalizer_iff_commutator_le_left.mp hHN
      (commutator_mem_commutator hxH hzK)
    exact hbout (hxz ▸ hm)
  have hKgen : K = closure ({x,y,b} : Set G) := by
    change H ⊔ zpowers b = _
    rw [hpair, zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext w
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hzN : z ∈ normalizer K := by
    have hconj (w c : G) (hw : ⁅w,z⁆ = c) : z * w * z⁻¹ = c⁻¹ * w := by
      have he := congrArg Inv.inv hw
      simp only [commutatorElement_def, mul_inv_rev, inv_inv] at he
      calc
        z * w * z⁻¹ = (z * w * z⁻¹ * w⁻¹) * w := by group
        _ = c⁻¹ * w := by rw [← he]; group
    rw [hKgen]
    apply involution_normalizes_closure hz
    intro w hw
    rcases hw with hw | hw | hw
    · rw [hw, hconj x b hxz, ← hKgen]
      exact K.mul_mem (K.inv_mem hbK) hxK
    · rw [hw, hconj y (a*b) hyz, ← hKgen]
      exact K.mul_mem (K.inv_mem (K.mul_mem haK hbK)) hyK
    · rw [Set.mem_singleton_iff.mp hw, hbz.symm.eq, mul_inv_cancel_right, ← hKgen]
      exact hbK
  have htriple : closure ({x,y,z} : Set G) = K ⊔ zpowers z := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro w hw
      rcases hw with hw | hw | hw
      · exact hw ▸ mem_sup_left hxK
      · exact hw ▸ mem_sup_left hyK
      · rw [Set.mem_singleton_iff.mp hw]
        exact mem_sup_right (mem_zpowers z)
    · apply sup_le
      · rw [hKgen]
        apply (closure_le _).mpr
        rintro w (rfl | rfl | rfl)
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
        · rw [← hxz]
          exact (closure ({x,y,z} : Set G)).mul_mem
            (mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
              (inv_mem (subset_closure (by simp)))) (inv_mem (subset_closure (by simp)))
      · exact zpowers_le.mpr (subset_closure (by simp))
  rw [htriple, card_sup_zpowers_of_normalizing_involution K z hz hzout hzN, hK]

end ThreeInvolutionFourCommutators
