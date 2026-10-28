module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureNonseedIncidence
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicals

/-!
# Point-core markings on the literal paired radicals

The aligned two-root construction retains its nonseed eight while purity
and the universal incidence theorem are applied. Thus both radicals in the
same original plane pair carry their literal point-core hyperplanes. The
same-package import-all edge intentionally reuses the private radical-pair
algebra without changing the frozen PairedRadicals owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The aligned plane sixteen retains its original nonseed eight until
all fifteen literal point-core intersections have been proved to be eights. -/
theorem TypeAt.exists_pure_plane_sixteen_point_cores (h : TypeAt z V) :
    ∃ W A : Subgroup G, W ≤ V ∧ Nat.card W = 4 ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ W ≤ A ∧
      A ≤ centralizer (W : Set G) ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      ∃ (u : G) (E : pointCoreEights u), u ∈ W ∧ u ≠ 1 ∧ TypeAt u V ∧
        E.val ∉ pointCoreSeedOrbit u V ∧ E.val ≤ A ∧
        A ⊓ (involutionCentralizer u).pCoreIn 2 = E.val := by
  obtain ⟨W, A, u, v, a, b, hWV, hW4, hAE, hA16, hWA, hAC, hAP,
    huW, hvW, hu1, hv1, huv, haQ, hbQ, haP, hbP, _, hjoin⟩ :=
    h.exists_aligned_elementary_sixteen
  let huT := h.at_seed_point u (hWV huW) hu1
  let hvT := h.at_seed_point v (hWV hvW) hv1
  have hVQ : V ≤ (involutionCentralizer u).pCoreIn 2 := by
    change V ≤ (pCore 2 (involutionCentralizer u)).map (involutionCentralizer u).subtype
    rw [← huT.centralizer_fitting]
    exact huT.seed_le_core
  let := hAE
  have haA : a ∈ A := by
    rw [hjoin]
    exact (show zpowers a ≤ W ⊔ (zpowers a ⊔ zpowers b) from
      le_sup_left.trans le_sup_right) (mem_zpowers a)
  have hbA : b ∈ A := by
    rw [hjoin]
    exact (show zpowers b ≤ W ⊔ (zpowers a ⊔ zpowers b) from
      le_sup_right.trans le_sup_right) (mem_zpowers b)
  let D := W ⊔ zpowers a
  have hDA : D ≤ A := sup_le hWA (zpowers_le.mpr haA)
  have hDQ : D ≤ (involutionCentralizer u).pCoreIn 2 :=
    sup_le (hWV.trans hVQ) (zpowers_le.mpr haQ)
  have hD8 : Nat.card D = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W a
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) a haA)
      (fun hh => haP (ambient_seed_le_core h (hWV hh)))
      (centralizer_le_normalizer _ (hAC haA)), hW4]
  have hDE : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.of_injective (inclusion hDA) (inclusion_injective hDA)
  let E : pointCoreEights u := ⟨D, hDQ, (show W ≤ D from le_sup_left) huW, hDE, hD8⟩
  have hEn := huT.eight_in_sixteen_not_seed E A hA16 hDA
  have hbE : b ∉ E.val := by
    intro hh
    have hboth : b ∈ (involutionCentralizer u).pCoreIn 2 ⊓
        (involutionCentralizer v).pCoreIn 2 := ⟨hDQ hh, hbQ⟩
    rw [h.distinct_point_cores_intersection u v (hWV huW) (hWV hvW) hu1 hv1 huv] at hboth
    exact hbP (ambient_seed_le_core h hboth)
  have hseedpure (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) : IsConj x z := by
    let := h.elementary
    apply h.centralizer_core_involution_isConj x
    · have hh := h.seed_le_core hx
      rwa [h.centralizer_fitting] at hh
    · exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hx1
  have hbz : IsConj b z :=
    (hvT.centralizer_core_involution_isConj b hbQ
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) b hbA)
        (fun hh => hbP (hh ▸ one_mem _)))).trans (hseedpure v (hWV hvW) hv1)
  have hCA := (huT.nonseed_eight_extension_structure E hEn A hDA hAE hA16).2.1
  have hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z := by
    intro x hx hx1
    by_cases hxE : x ∈ E.val
    · exact (huT.centralizer_core_involution_isConj x (hDQ hxE)
        (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hx1)).trans
          (hseedpure u (hWV huW) hu1)
    · obtain ⟨q, _, hq⟩ := huT.nonseed_extension_exterior_transitive E hEn A hA16 hDA b hbA hbE x hx hxE
      exact (isConj_iff.mpr ⟨q, hq⟩).symm.trans hbz

  have hpoints := huT.pure_nonseed_extension_point_core_eights E hEn A hA16 hDA
    (fun x hx hx1 => (hpure x hx hx1).trans (hseedpure u (hWV huW) hu1).symm)
  have hAQ := (huT.nonseed_eight_extension_structure E hEn A hDA hAE hA16).2.2
  exact ⟨W, A, hWV, hW4, hAE, hA16, hWA, hAC, hAP, hCA, hpure, hpoints,
    u, E, huW, hu1, huT, hEn, hDA, hAQ⟩

/-- Original HS data construct two pure elementary-sixteen radicals whose
literal intersection is the original seed plane and whose join has order64.
The second is conjugate by an actual element of the whole cyclic-four core. -/
theorem TypeAt.exists_point_marked_paired_plane_radicals (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p : G), W ≤ V ∧ Nat.card W = 4 ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧
      A ≤ normalizer (B : Set G) ∧ B ≤ normalizer (A : Set G) ∧
      Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      normalizer (A : Set G) ⊓ normalizer (B : Set G) =
        normalizer (A : Set G) ⊓ normalizer (W : Set G) := by
  obtain ⟨W, A, hWV, hW4, hAE, hA16, hWA, hAC, hAP, hCA, hpure, hpoints, _⟩ :=
    h.exists_pure_plane_sixteen_point_cores
  let := hAE
  obtain ⟨p, hp, hpW⟩ := exists_root_outside h W hWV hW4
  let B := A.map (MulAut.conj p).toMonoidHom
  let e : A ≃* B := A.equivMapOfInjective (MulAut.conj p).toMonoidHom (MulAut.conj p).injective
  have hBE : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hB16 : Nat.card B = 16 := (Nat.card_congr e.toEquiv).symm.trans hA16
  obtain ⟨hi, hc⟩ := conjugate_pair h W A hWV hW4 hWA hAC hAP p hp hpW
  change A ⊓ B = W at hi
  change ⁅A, B⁆ ≤ W at hc
  have hWB : W ≤ B := hi ▸ (show A ⊓ B ≤ B from inf_le_right)
  have hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W := by
    apply le_antisymm
    · rintro x ⟨⟨a, ha, rfl⟩, hxP⟩
      have haP : a ∈ (normalizer (V : Set G)).pCoreIn 2 := by
        have hh := mul_mem (mul_mem (inv_mem hp) hxP) hp
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_mul_cancel_left,
          mul_assoc, inv_mul_cancel, mul_one] using hh
      have haW : a ∈ W := hAP ▸ (show a ∈ A ⊓ (normalizer (V : Set G)).pCoreIn 2 from ⟨ha, haP⟩)
      change p * a * p⁻¹ ∈ W
      let := core_abelian h
      rwa [show p * a = a * p from setLike_mul_comm hp haP, mul_inv_cancel_right]
    · exact le_inf hWB (hWV.trans (ambient_seed_le_core h))
  have hCB : centralizer (B : Set G) = B := by
    have hh := map_centralizer_equiv (A : Set G) (MulAut.conj p)
    rw [hCA] at hh
    exact hh.symm
  have hAB : A ≤ normalizer (B : Set G) := le_normalizer_iff_commutator_le_right.mpr (hc.trans hWB)
  have hBA : B ≤ normalizer (A : Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans hWA)
  have h64 : Nat.card (A ⊔ B : Subgroup G) = 64 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hBA
    rw [hA16, hB16, hi, hW4] at hh
    omega
  have hBC : B ≤ centralizer (W : Set G) := by
    rintro b ⟨a, ha, rfl⟩ w hw
    have hpw : Commute p w := by
      let := core_abelian h
      exact setLike_mul_comm hp (ambient_seed_le_core h (hWV hw))
    have haw : Commute a w := (hAC ha w hw).symm
    exact ((hpw.mul_left haw).mul_left hpw.inv_left).eq.symm
  have hpointsB : ∀ x ∈ B, x ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8 := by
    rintro x ⟨a, ha, rfl⟩ hx1
    have ha1 : a ≠ 1 := fun ha1 => hx1 (by simp only [ha1, map_one])
    have hh : (A ⊓ (involutionCentralizer a).pCoreIn 2 : Subgroup G).map
        (MulAut.conj p).toMonoidHom =
        B ⊓ (involutionCentralizer ((MulAut.conj p).toMonoidHom a)).pCoreIn 2 := by
      rw [map_inf _ _ _ (MulAut.conj p).injective, pointCore_conjugate]
      rfl
    rw [← hh, card_map_of_injective (MulAut.conj p).injective]
    exact hpoints a ha ha1
  refine ⟨W, A, B, p, hWV, hW4, hAE, hA16, hBE, hB16, hp, hpW, rfl,
    hAP, hBP, hCA, hCB, hi, hc, hAB, hBA, h64, sup_le hAC hBC, hpure, ?_,
    hpoints, hpointsB, h.paired_plane_radicals_normalizer W A hWV hW4 hA16 hWA hAC hAP p hp hpW⟩
  rintro x ⟨a, ha, rfl⟩ hx1
  have ha1 : a ≠ 1 := fun ha1 => hx1 (by simp only [ha1, map_one])
  exact (isConj_iff.mpr ⟨p, rfl⟩).symm.trans (hpure a ha ha1)

end CFSG.Quasithin.HigmanSims
