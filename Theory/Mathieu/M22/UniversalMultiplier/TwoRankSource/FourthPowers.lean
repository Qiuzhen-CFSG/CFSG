module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoRankSource
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.Reduction
public import Theory.GroupTheory.ClassTwoCommutator

/-!
# The fourth-power bound for native M₂₂ kernels

The full hexad translation preimage has central squares and commutators
of exponent two. Its fourth-power map is therefore a homomorphism into
the original central kernel, invariant under the lifted native A₆ section.
Extend it across the genuine split hexad preimage. Global perfectness and
odd-index transfer put the central two-kernel in that preimage's derived
subgroup, so every kernel element has fourth power one.

Together with cyclicity, this bounds a two-kernel by four. The existing
odd-kernel reduction gives the arbitrary-cover exclusion of eight.
Source: Aschbacher–Smith I.1.3(4), printed p.407, and native hexad geometry
I.2.2(6), printed p.412. No perfectness of the local preimage is assumed.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace Sporadic.Mathieu.M22UniversalMultiplier.TwoRankSource

private theorem square_product_of_central_squares {R : Type*} [Group R]
    (hd : commutator R ≤ center R) (x y : R) (hx : x ^ 2 ∈ center R) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
  have hc := hd (commutator_mem_commutator (mem_top x) (mem_top y))
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := mem_center_iff.mp hc _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [mem_center_iff.mp hx]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

private theorem fourth_product_of_central_squares {R : Type*} [Group R]
    (hd : commutator R ≤ center R) (hsq : ∀ x : R, x ^ 2 ∈ center R)
    (x y : R) : (x * y) ^ 4 = x ^ 4 * y ^ 4 := by
  have hc := hd (commutator_mem_commutator (mem_top x) (mem_top y))
  have hc2 : ⁅x,y⁆ ^ 2 = 1 := by
    have hp := map_pow (ClassTwo.commutatorHom hd x) y 2
    change ⁅x,y ^ 2⁆ = ⁅x,y⁆ ^ 2 at hp
    rw [← hp]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hsq y) x)
  calc
    (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (x ^ 2 * y ^ 2 * ⁅x,y⁆) ^ 2 := by rw [square_product_of_central_squares hd x y (hsq x)]
    _ = (x ^ 2 * y ^ 2) ^ 2 * ⁅x,y⁆ ^ 2 :=
      (show Commute (x ^ 2 * y ^ 2) ⁅x,y⁆ from mem_center_iff.mp hc _).mul_pow 2
    _ = (x ^ 2) ^ 2 * (y ^ 2) ^ 2 := by
      rw [hc2, mul_one, (show Commute (x ^ 2) (y ^ 2) from mem_center_iff.mp (hsq y) _).mul_pow]
    _ = x ^ 4 * y ^ 4 := by rw [← pow_mul, ← pow_mul]

/-- Global transfer kills the fourth power of every element of a central two-kernel. -/
theorem twoPrimary_kernel_fourth_eq_one {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) (hp : IsPGroup 2 f.toMonoidHom.ker)
    (c : f.toMonoidHom.ker) : c ^ 4 = 1 := by
  let C := f.toMonoidHom.ker
  let : IsMulCommutative C := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (f.ker_le_center y.property) x)⟩⟩
  let B := (m22SetAction m22Hexad123).ker
  let : B.Normal := inferInstanceAs (m22SetAction m22Hexad123).ker.Normal
  let : IsElementaryAbelian 2 B := m22HexadKernel_elementaryAbelian m22Hexad123_mem
  let P := m22HexadStabilizer.comap f.toMonoidHom
  let q : P →* m22HexadStabilizer :=
    (f.toMonoidHom.comp P.subtype).codRestrict _ (fun x => x.property)
  let N := B.comap q
  let : N.Normal := ⟨fun x hx g => by
    change q (g * x * g⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv]
    exact (inferInstance : B.Normal).conj_mem (q x) hx (q g)⟩
  let qN : N →* B := (q.comp N.subtype).codRestrict _ (fun x => x.property)
  have hqNc : qN.ker ≤ center N := by
    intro x hx
    have hfx : f.toMonoidHom x.val.val = 1 :=
      congrArg (fun v : B => (v.val : M22)) hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_center_iff.mp (f.ker_le_center hfx) y.val.val
  have hd : commutator N ≤ center N := (Abelianization.commutator_subset_ker qN).trans hqNc
  have hsq (x : N) : x ^ 2 ∈ center N := by
    apply hqNc
    rw [MonoidHom.mem_ker, map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) (qN x)
  have hfour (x : N) : x.val.val ^ 4 ∈ C := by
    change f.toMonoidHom (x.val.val ^ 4) = 1
    rw [map_pow]
    have hx : (qN x) ^ 4 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      ((IsElementaryAbelian.exponent_dvd_p 2 B).trans (by decide : 2 ∣ 4)) (qN x)
    exact congrArg (fun v : B => (v.val : M22)) hx
  let fourth : N →* C := {
    toFun := fun x => ⟨x.val.val ^ 4, hfour x⟩
    map_one' := Subtype.ext (one_pow 4)
    map_mul' := by
      intro x y
      apply Subtype.ext
      exact congrArg (fun n : N => n.val.val) (fourth_product_of_central_squares hd hsq x y) }
  obtain ⟨s, hs⟩ := exists_hexadSection_lift f.toMonoidHom f.surjective f.ker_le_center hp
    m22Hexad123_mem
  let j := m22HexadSection m22Hexad123_mem
  let S : alternatingGroup (Fin 6) →* P := s.codRestrict P (by
    intro a
    change f.toMonoidHom (s a) ∈ m22HexadStabilizer
    rw [show f.toMonoidHom (s a) = (j a : M22) from DFunLike.congr_fun hs a]
    exact (j a).property)
  have hqS (a : alternatingGroup (Fin 6)) : q (S a) = j a :=
    Subtype.ext (DFunLike.congr_fun hs a)
  let β : P →* alternatingGroup (Fin 6) := (m22HexadMarking m22Hexad123_mem).symm.toMonoidHom.comp
    ((m22HexadSixMap m22Hexad123_mem).comp q)
  have hβS (a : alternatingGroup (Fin 6)) : β (S a) = a := by
    change (m22HexadMarking m22Hexad123_mem).symm
      (m22HexadSixMap m22Hexad123_mem (q (S a))) = a
    rw [hqS, m22HexadSixMap_section, MulEquiv.symm_apply_apply]
  have hβiff (x : P) : β x = 1 ↔ x ∈ N := by
    change (m22HexadMarking m22Hexad123_mem).symm
      (m22HexadSixMap m22Hexad123_mem (q x)) = 1 ↔ q x ∈ B
    rw [map_eq_one_iff _ (m22HexadMarking m22Hexad123_mem).symm.injective]
    change q x ∈ (m22HexadSixMap m22Hexad123_mem).ker ↔ q x ∈ B
    rw [m22HexadSixMap_ker]
  have hβN (x : N) : β x.val = 1 := (hβiff x.val).mpr x.property
  let α : alternatingGroup (Fin 6) →* MulAut N := MulAut.conjNormal.comp S
  let kP : N ⋊[α] alternatingGroup (Fin 6) →* P :=
    SemidirectProduct.lift N.subtype S (by intro a; apply MonoidHom.ext; intro x; rfl)
  have hβk (x : N ⋊[α] alternatingGroup (Fin 6)) : β (kP x) = x.right := by
    change β (x.left.val * S x.right) = _
    rw [map_mul, hβN, hβS, one_mul]
  have hkPi : Function.Injective kP := by
    apply kP.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have ha : x.right = 1 := (hβk x).symm.trans ((congrArg β hx).trans β.map_one)
    have hn : x.left = 1 := by
      apply Subtype.ext
      change x.left.val * S x.right = 1 at hx
      rwa [ha, map_one, mul_one] at hx
    exact SemidirectProduct.ext hn ha
  have hkPs : Function.Surjective kP := by
    intro x
    let n : N := ⟨x * (S (β x))⁻¹, (hβiff _).mp (by
      rw [map_mul, map_inv, hβS, mul_inv_cancel])⟩
    exact ⟨⟨n, β x⟩, inv_mul_cancel_right x (S (β x))⟩
  let eP : N ⋊[α] alternatingGroup (Fin 6) ≃* P := MulEquiv.ofBijective kP ⟨hkPi, hkPs⟩
  have hfa (a : alternatingGroup (Fin 6)) (x : N) : fourth (α a x) = fourth x := by
    apply Subtype.ext
    change (MulAut.conj (s a) x.val.val) ^ 4 = x.val.val ^ 4
    rw [← map_pow]
    change s a * x.val.val ^ 4 * (s a)⁻¹ = x.val.val ^ 4
    rw [mem_center_iff.mp (f.ker_le_center (hfour x)) (s a), mul_inv_cancel_right]
  let F₀ : N ⋊[α] alternatingGroup (Fin 6) →* C := SemidirectProduct.lift fourth 1 (by
    intro a
    apply MonoidHom.ext
    intro x
    simpa using hfa a x)
  let F : P →* C := F₀.comp eP.symm.toMonoidHom
  let : Group.IsPerfect E := f.isPerfect
  have hCP : C ≤ P := f.toMonoidHom.ker_le_comap m22HexadStabilizer
  have hindex : ¬ 2 ∣ P.index := by
    have hh := m22HexadStabilizer.card_mul_index
    rw [m22HexadStabilizer_card, m22_order] at hh
    have hi : m22HexadStabilizer.index = 77 := by omega
    rw [show P.index = m22HexadStabilizer.index from
      index_comap_of_surjective _ f.surjective, hi]
    decide
  have hCcomm := central_pSubgroup_le_commutator P C hCP f.ker_le_center hp hindex
  let cp : P := ⟨c.val, hCP c.property⟩
  have hcq : q cp = 1 := Subtype.ext c.property
  let cn : N := ⟨cp, by change q cp ∈ B; rw [hcq]; exact B.one_mem⟩
  have hcp : cp ∈ commutator P := by
    have hh := hCcomm c.property
    rw [← map_subtype_commutator] at hh
    obtain ⟨y, hy, he⟩ := hh
    have hyc : y = cp := Subtype.ext he
    exact hyc ▸ hy
  have hF : F cp = 1 := Abelianization.commutator_subset_ker F hcp
  have heP : eP.symm cp = ⟨cn, 1⟩ := by
    apply eP.injective
    rw [eP.apply_symm_apply]
    change cp = cn.val * S 1
    rw [map_one, mul_one]
  change F₀ (eP.symm cp) = 1 at hF
  rw [heP] at hF
  change fourth cn * 1 = 1 at hF
  rw [mul_one] at hF
  exact Subtype.ext (congrArg Subtype.val hF)

/-- The cyclicity and fourth-power arguments bound every native two-kernel by four. -/
theorem twoPrimary_kernel_card_dvd_four {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) (hp : IsPGroup 2 f.toMonoidHom.ker) :
    Nat.card f.toMonoidHom.ker ∣ 4 := by
  have hc := twoPrimary_kernel_isCyclic f hp
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (twoPrimary_kernel_fourth_eq_one f hp)
  rwa [hc.exponent_eq_card] at h

/-- The full arbitrary-cover two-primary upper bound, using the existing odd-kernel reduction. -/
theorem not_eight_dvd_kernel {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) : ¬ 8 ∣ Nat.card f.toMonoidHom.ker :=
  not_eight_dvd_kernel_of_twoPrimary_bound
    (fun _ _ _ g hp => Nat.le_of_dvd (by decide) (twoPrimary_kernel_card_dvd_four g hp)) f

end Sporadic.Mathieu.M22UniversalMultiplier.TwoRankSource
