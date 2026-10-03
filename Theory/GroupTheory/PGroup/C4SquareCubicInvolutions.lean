module

public import Theory.GroupTheory.PGroup.C4SquareCubicCore

/-!
# Cubic orbits and the split involution cover

For a core element r, its cubic norm r a(r) a²(r) is carried by a to a
conjugate. The fixed-free action on the quotient puts this norm in the
base. Its central square is fixed by a, so the norm has square one and
is central. It is then fixed by a itself and equals one.

Consequently a core involution commutes with its cubic image. These two
involutions and the central omega generate an elementary sixteen. Its
conjugate by the outside involution is a distinct elementary sixteen;
the centralizer calculation makes their intersection exactly the central
omega. Their product is the core, and a product of elements from the two
sixteens is an involution only when one factor belongs to the intersection.
This proves the split/nonsplit involution dichotomy directly, without
classifying the core by a presentation.

Source: MacWilliams, Trans. AMS 150 (1970), Lemma 3 and the inside-involution
calculation, printed pp.380–384, DOI 10.1090/S0002-9947-1970-0276324-3.
-/
open Subgroup
open scoped IsMulCommutative commutatorElement Pointwise
namespace C4SquareCubicInvertingExtension
variable {P : Type*} [Group P] [Finite P]
  {C R : Subgroup P} {a : MulAut P} {t : P}
  (h : C4SquareCubicInvertingExtension C R a t)
  (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
  (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
  (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
  (e : C ≃* C4SquareExtension.Model)
  (ha : orderOf a = 3) (hfree : ∀ c ∈ C, a c = c → c = 1)

include h hC hno hZ e ha hfree in
/-- The cubic norm of every core element is one. -/
public theorem core_cubic_norm_eq_one (r : P) (hr : r ∈ R) : r * a r * a (a r) = 1 := by
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hcycle (x : P) : a (a (a x)) = x := by
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using
      congrArg (fun b : MulAut P => b x) ha3
  let n := r * a r * a (a r)
  have hnR : n ∈ R := R.mul_mem (R.mul_mem hr (h.core_invariant r hr))
    (h.core_invariant (a r) (h.core_invariant r hr))
  have han : a n = r⁻¹ * n * r := by
    dsimp only [n]
    rw [map_mul, map_mul, hcycle]
    group
  have hnC : n ∈ C := by
    apply h.core_quotient_fixed_free n hnR
    apply omega_le_base hC hno hZ
    rw [han]
    simpa only [commutatorElement_def, inv_inv] using
      h.core_commutator_mem_omega hC hno hZ e r⁻¹ n (R.inv_mem hr) hnR
  have hs : n ^ 2 ∈ center P := map_subtype_le _ (h.core_square_mem_omega hC hno hZ e n hnR)
  have hnsq : n ^ 2 = 1 := by
    apply hfree _ (C.pow_mem hnC 2)
    calc
      a (n ^ 2) = (r⁻¹ * n * r) ^ 2 := by rw [map_pow, han]
      _ = r⁻¹ * n ^ 2 * r := by simp only [pow_two]; group
      _ = n ^ 2 := by rw [(mem_center_iff.mp hs) r⁻¹]; group
  have hnZ : n ∈ center P := map_subtype_le _
    (hC.mem_omega_center_of_square_eq_one hno hZ hnC hnsq)
  apply hfree n hnC
  rw [han, (mem_center_iff.mp hnZ) r⁻¹]
  group

include h hC hno hZ e ha hfree in
/-- A core involution commutes with its cubic image. -/
public theorem core_involution_commute_cubic_image (u : P) (huR : u ∈ R) (hu2 : u ^ 2 = 1) :
    Commute u (a u) := by
  have hav : (a u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have haw : (a (a u)) ^ 2 = 1 := by rw [← map_pow, ← map_pow, hu2, map_one, map_one]
  have hm : (u * a u) ^ 2 = 1 := by
    have hn := h.core_cubic_norm_eq_one hC hno hZ e ha hfree u huR
    have heq : u * a u = (a (a u))⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [heq, inv_pow, haw, inv_one]
  have hiu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hu2)
  have hiv : (a u)⁻¹ = a u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hav)
  have him : (u * a u)⁻¹ = u * a u :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hm)
  change u * a u = a u * u
  simpa only [mul_inv_rev, hiu, hiv] using him.symm

include h hC hno hZ e ha hfree in
/-- A non-base core involution and its cubic image generate an elementary sixteen over the central omega. -/
public theorem exists_elementary_sixteen_of_core_involution (u : P) (huR : u ∈ R)
    (huC : u ∉ C) (hu2 : u ^ 2 = 1) :
    ∃ A : Subgroup P, A ≤ R ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      u ∈ A ∧ (omega₁ (center P) (p := 2)).map (center P).subtype ≤ A := by
  classical
  let W := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hWC : W ≤ C := omega_le_base hC hno hZ
  let : W.Normal := ⟨fun w hw g => by
    rw [(mem_center_iff.mp (map_subtype_le _ hw)) g, mul_inv_cancel_right]
    exact hw⟩
  let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  have hWcent (x : P) : x ∈ centralizer (W : Set P) := by
    intro w hw
    exact (mem_center_iff.mp (map_subtype_le _ hw) x).symm
  let : IsElementaryAbelian 2 (zpowers u) := IsElementaryAbelian.zpowers_of_pow_eq_one hu2
  have hav : (a u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  let : IsElementaryAbelian 2 (zpowers (a u)) := IsElementaryAbelian.zpowers_of_pow_eq_one hav
  let U := W ⊔ zpowers u
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.sup_of_le_centralizer
    (zpowers_le.mpr (hWcent u))
  have huc : Commute u (a u) := h.core_involution_commute_cubic_image hC hno hZ e ha hfree u huR hu2
  have hvU : a u ∈ centralizer (U : Set P) := by
    have hUc : U ≤ centralizer ({a u} : Set P) := sup_le
      ((map_subtype_le _).trans (center_le_centralizer _))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr huc.eq))
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hUc hz)
  let A := U ⊔ zpowers (a u)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hvU)
  have hUcard : Nat.card U = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W u hu2 (fun hu => huC (hWC hu))
      (centralizer_le_normalizer _ (hWcent u)),
      card_map_of_injective (center P).subtype_injective, hZ]
  have hvnot : a u ∉ U := by
    intro hv
    obtain ⟨w, hw, z, hz, heq⟩ := mem_sup_of_normal_left.mp hv
    have horder : orderOf u = 2 := orderOf_eq_prime hu2 (fun hu => huC (hu ▸ C.one_mem))
    have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hu2⟩
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, horder] at hz
    obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hz
    have hil : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · have hz1 : z = 1 := by simpa using hiz.symm
      have hauC : a u ∈ C := by rw [← heq, hz1, mul_one]; exact hWC hw
      let : C.Characteristic := hC.characteristic
      have hh := (characteristic_iff_le_comap.mp (inferInstance : C.Characteristic) a.symm) hauC
      exact huC (by simpa using hh)
    · have hzu : z = u := by simpa using hiz.symm
      apply huC (h.core_quotient_fixed_free u huR ?_)
      rw [← heq, hzu, mul_inv_cancel_right]
      exact hWC hw
  refine ⟨A, sup_le (sup_le (hWC.trans h.base_le) (zpowers_le.mpr huR))
    (zpowers_le.mpr (h.core_invariant u huR)), inferInstance, ?_,
    (show U ≤ A from le_sup_left) ((show zpowers u ≤ U from le_sup_right) (mem_zpowers u)),
    (show W ≤ U from le_sup_left).trans le_sup_left⟩
  rw [card_sup_zpowers_of_normalizing_involution U (a u) hav hvnot
    (centralizer_le_normalizer _ hvU), hUcard]

include h hC hno hZ e ha hfree in
/-- Either all core involutions lie in the base, or two elementary sixteens cover them. -/
public theorem core_involution_dichotomy :
    (∀ u ∈ R, u ^ 2 = 1 → u ∈ C) ∨
      ∃ X Y : Subgroup P, SplitInvolutionCover R X Y := by
  classical
  by_cases hbase : ∀ u ∈ R, u ^ 2 = 1 → u ∈ C
  · exact Or.inl hbase
  · right
    push Not at hbase
    obtain ⟨u, huR, hu2, huC⟩ := hbase
    obtain ⟨X, hXR, hX, hXcard, _, hWX⟩ :=
      h.exists_elementary_sixteen_of_core_involution hC hno hZ e ha hfree u huR huC hu2
    let W := (omega₁ (center P) (p := 2)).map (center P).subtype
    let Y := X.map (MulAut.conj t).toMonoidHom
    let : R.Normal := R.normal_of_index_eq_two h.core_index
    let : IsElementaryAbelian 2 X := hX
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
    have hY : IsElementaryAbelian 2 Y := inferInstance
    have hYcard : Nat.card Y = 16 := by
      rw [card_map_of_injective (MulAut.conj t).injective, hXcard]
    have hYR : Y ≤ R := by
      rintro y ⟨x, hx, rfl⟩
      exact (inferInstance : R.Normal).conj_mem x (hXR hx) t
    have hWY : W ≤ Y := by
      intro w hw
      refine ⟨w, hWX hw, ?_⟩
      change t * w * t⁻¹ = w
      rw [(mem_center_iff.mp (map_subtype_le _ hw)) t, mul_inv_cancel_right]
    have hNX : normalizer (X : Set P) = R :=
      h.normalizer_elementary_sixteen_eq_core hno X hX hXcard
        (h.core_le_normalizer_of_omega_le hC hno hZ e X hXR hWX)
    have hne : X ≠ Y := by
      intro heq
      have ht : t ∈ normalizer (X : Set P) := mem_normalizer_iff_map_conj_eq.mpr heq.symm
      exact h.outside_not_mem (hNX ▸ ht)
    have hinf : X ⊓ Y = W := by
      apply le_antisymm
      · intro z hz
        by_contra hzW
        have hzC : z ∉ C := by
          intro hzC
          exact hzW (hC.mem_omega_center_of_square_eq_one hno hZ hzC
            (elemPow_eq_one_of_isElementaryAbelian z hz.1))
        have hx := h.centralizer_eq_of_elementary_sixteen hC hno hZ e X hX hXcard z
          hz.1 (hXR hz.1) hzC
        have hy := h.centralizer_eq_of_elementary_sixteen hC hno hZ e Y hY hYcard z
          hz.2 (hYR hz.2) hzC
        exact hne (hx.symm.trans hy)
      · exact le_inf hWX hWY
    have hYN : Y ≤ normalizer (X : Set P) := by rw [hNX]; exact hYR
    have hsup : X ⊔ Y = R := by
      have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes X Y hYN
      rw [hXcard, hYcard, hinf, card_map_of_injective (center P).subtype_injective, hZ] at hc
      apply eq_of_le_of_card_ge (sup_le hXR hYR)
      rw [h.core_card]
      omega
    refine ⟨X, Y, ⟨hXR, hYR, hX, hY, hXcard, hYcard, hinf, ?_⟩⟩
    intro v hvR hv2
    have hvprod : v ∈ (X : Set P) * (Y : Set P) := by
      rw [← coe_mul_of_right_le_normalizer_left X Y hYN]
      exact hsup.symm ▸ hvR
    obtain ⟨x, hx, y, hy, hxy⟩ := hvprod
    have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
    have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hy
    have hix : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
    have hiy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
    have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right
      (by simpa only [← pow_two, hxy] using hv2)
    have hcomm : x * y = y * x := by
      simpa only [mul_inv_rev, hix, hiy] using hxyi.symm
    by_cases hxW : x ∈ W
    · exact Or.inr (hxy ▸ Y.mul_mem (hWY hxW) hy)
    · have hxC : x ∉ C := by
        intro hxC
        exact hxW (hC.mem_omega_center_of_square_eq_one hno hZ hxC hx2)
      have hyX : y ∈ X := by
        rw [← h.centralizer_eq_of_elementary_sixteen hC hno hZ e X hX hXcard x hx (hXR hx) hxC]
        exact mem_centralizer_singleton_iff.mpr hcomm.symm
      exact Or.inl (hxy ▸ X.mul_mem hx hyX)

end C4SquareCubicInvertingExtension
