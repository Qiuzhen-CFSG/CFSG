module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AlignedElementarySixteen
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExteriorTransitivity
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenIntersectionNonseed
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Two actual sixteen radicals over the original seed plane

A square root in the whole cyclic-four core, whose square is outside the
fixed plane, conjugates an elementary sixteen to a second one meeting it
in exactly that plane. Commutators of the two groups lie in the plane,
so their literal join has order sixty-four. No endpoint or complement
marking is an input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private noncomputable def coordinates (h : TypeAt z V) :
    (normalizer (V : Set G)).pCoreIn 2 ≃* (Fin 3 → Multiplicative (ZMod 4)) :=
  ((pCore 2 (normalizer (V : Set G))).equivMapOfInjective
    (normalizer (V : Set G)).subtype (normalizer (V : Set G)).subtype_injective).symm.trans
    ((MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans h.normalizer_core.some)

private theorem core_abelian (h : TypeAt z V) :
    IsMulCommutative ((normalizer (V : Set G)).pCoreIn 2) :=
  ⟨⟨fun a b => (coordinates h).injective (by simp only [map_mul, mul_comm])⟩⟩

private theorem ambient_seed_le_core (h : TypeAt z V) :
    V ≤ (normalizer (V : Set G)).pCoreIn 2 := by
  change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
  rw [← h.normalizer_fitting]
  exact h.seed_le_normalizer_core

private theorem core_square_one (h : TypeAt z V) (q : G)
    (hq : q ∈ (normalizer (V : Set G)).pCoreIn 2) (hq2 : q ^ 2 = 1) : q ∈ V := by
  obtain ⟨qM, hqM, heq⟩ := hq
  have hqV : qM ∈ V.subgroupOf (normalizer (V : Set G)) := by
    rw [h.seed_eq_omega_normalizer_core]
    refine ⟨⟨qM, hqM⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change (qM : G) ^ 2 = 1
    rwa [show (qM : G) = q from heq]
  exact heq ▸ hqV

private theorem core_square_seed (h : TypeAt z V) (q : G)
    (hq : q ∈ (normalizer (V : Set G)).pCoreIn 2) : q ^ 2 ∈ V := by
  apply core_square_one h _ (pow_mem hq 2)
  have he : ∀ t : Multiplicative (ZMod 4), (t ^ 2) ^ 2 = 1 := by decide +kernel
  have hh : ((⟨q, hq⟩ : (normalizer (V : Set G)).pCoreIn 2) ^ 2) ^ 2 = 1 := by
    apply (coordinates h).injective
    simp only [map_pow, map_one]
    exact funext fun i => he (coordinates h ⟨q, hq⟩ i)
  exact congrArg Subtype.val hh

private theorem core_normalized (_h : TypeAt z V) :
    normalizer (V : Set G) ≤ normalizer ((normalizer (V : Set G)).pCoreIn 2 : Set G) := by
  have hh := (pCore 2 (normalizer (V : Set G))).le_normalizer_map
    (normalizer (V : Set G)).subtype
  rw [(pCore 2 (normalizer (V : Set G))).normalizer_eq_top,
    ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh

private theorem fixed_seed (h : TypeAt z V) (W : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (a : G)
    (haC : a ∈ centralizer (W : Set G))
    (haP : a ∉ (normalizer (V : Set G)).pCoreIn 2)
    (v : G) (hv : v ∈ V) : Commute a v ↔ v ∈ W := by
  let := h.elementary
  constructor
  · intro hav
    by_contra hvW
    have hvN : v ∈ normalizer (W : Set G) := centralizer_le_normalizer _
      (fun w hw => setLike_mul_comm (hWV hw) hv)
    have he : W ⊔ zpowers v = V := by
      apply eq_of_le_of_card_ge (sup_le hWV (zpowers_le.mpr hv))
      rw [card_sup_zpowers_of_normalizing_involution W v
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hvW hvN, hW4, h.seed_card]
    apply haP
    change a ∈ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.seed_centralizer]
    have hh : W ⊔ zpowers v ≤ involutionCentralizer a :=
      sup_le (fun w hw => mem_centralizer_singleton_iff.mpr (haC w hw))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hav.eq.symm))
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hh (he.symm ▸ hw))
  · exact fun hvW => (haC v hvW).symm

private theorem displacement_core (h : TypeAt z V) (a d : G)
    (ha : a ∈ normalizer (V : Set G))
    (hd : d ∈ (normalizer (V : Set G)).pCoreIn 2) :
    ⁅a, d⁆ ∈ (normalizer (V : Set G)).pCoreIn 2 := by
  exact mul_mem ((mem_normalizer_iff.mp (core_normalized h ha) d).mp hd) (inv_mem hd)

private theorem displacement_square (h : TypeAt z V) (a d : G)
    (ha : a ∈ normalizer (V : Set G))
    (hd : d ∈ (normalizer (V : Set G)).pCoreIn 2) :
    ⁅a, d⁆ ^ 2 = ⁅a, d ^ 2⁆ := by
  let := core_abelian h
  have hc : Commute (a * d * a⁻¹) d⁻¹ := setLike_mul_comm
    ((mem_normalizer_iff.mp (core_normalized h ha) d).mp hd) (inv_mem hd)
  rw [commutatorElement_def, hc.mul_pow]
  simp only [commutatorElement_def, pow_two]
  group

omit [Finite G] in
private theorem displacement_fixed (a d : G) (ha2 : a ^ 2 = 1)
    (hd2 : ⁅a, d⁆ ^ 2 = 1) : Commute a ⁅a, d⁆ := by
  have ha : a * a = 1 := by simpa only [pow_two] using ha2
  have hd : ⁅a, d⁆⁻¹ = ⁅a, d⁆ := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hd2)
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    a * ⁅a, d⁆ * a⁻¹ = ⁅a, d⁆⁻¹ := by
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
      simp only [commutatorElement_def, mul_inv_rev, inv_inv, hai]
      simp only [← mul_assoc, ha, one_mul]
    _ = ⁅a, d⁆ := hd

private theorem plane_displacement (h : TypeAt z V) (W : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (a d : G)
    (haC : a ∈ centralizer (W : Set G)) (ha2 : a ^ 2 = 1)
    (hd : d ∈ (normalizer (V : Set G)).pCoreIn 2) (hdW : d ^ 2 ∈ W) :
    ⁅a, d⁆ ∈ W := by
  have haM := h.plane_centralizer_le_normalizer W hWV hW4 haC
  by_cases haP : a ∈ (normalizer (V : Set G)).pCoreIn 2
  · let := core_abelian h
    rw [(show Commute a d from setLike_mul_comm haP hd).commutator_eq]
    exact one_mem _
  have hds : ⁅a, d⁆ ^ 2 = 1 := by
    rw [displacement_square h a d haM hd]
    exact (show Commute a (d ^ 2) from (haC _ hdW).symm).commutator_eq
  exact (fixed_seed h W hWV hW4 a haC haP _
    (core_square_one h _ (displacement_core h a d haM hd) hds)).mp
      (displacement_fixed a d ha2 hds)

private theorem exists_root_outside (h : TypeAt z V) (W : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) :
    ∃ p ∈ (normalizer (V : Set G)).pCoreIn 2, p ^ 2 ∉ W := by
  have hn : ¬ V ≤ W := by
    intro he
    have hc := congrArg (fun S : Subgroup G => Nat.card S) (le_antisymm he hWV)
    rw [h.seed_card, hW4] at hc
    omega
  obtain ⟨v, hv, hvW⟩ := Set.not_subset.mp hn
  let := h.elementary
  have hrv : ∀ a : Multiplicative (ZMod 4), a ^ 2 = 1 → ∃ b, b ^ 2 = a := by decide +kernel
  let vP : (normalizer (V : Set G)).pCoreIn 2 := ⟨v, ambient_seed_le_core h hv⟩
  have hv2 : vP ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
  have hr (i : Fin 3) : ∃ b : Multiplicative (ZMod 4), b ^ 2 = coordinates h vP i :=
    hrv _ (by simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using
      congrArg (fun q => coordinates h q i) hv2)
  choose r hr using hr
  let p := (coordinates h).symm r
  have hp : p ^ 2 = vP := (coordinates h).injective (by
    rw [map_pow, MulEquiv.apply_symm_apply]
    exact funext hr)
  refine ⟨p, p.property, ?_⟩
  rw [← Subgroup.coe_pow, hp]
  exact hvW

private theorem conjugate_pair (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W) :
    let B := A.map (MulAut.conj p).toMonoidHom
    A ⊓ B = W ∧ ⁅A, B⁆ ≤ W := by
  let P := (normalizer (V : Set G)).pCoreIn 2
  let B := A.map (MulAut.conj p).toMonoidHom
  let := core_abelian h
  have hAM : A ≤ normalizer (V : Set G) :=
    hAC.trans (h.plane_centralizer_le_normalizer W hWV hW4)
  have hWP : W ≤ P := hWV.trans (ambient_seed_le_core h)
  have hWB : W ≤ B := by
    intro w hw
    refine ⟨w, hWA hw, ?_⟩
    change p * w * p⁻¹ = w
    rw [show p * w = w * p from setLike_mul_comm hp (hWP hw), mul_inv_cancel_right]
  have hpair : A ⊓ B = W := by
    apply le_antisymm
    · rintro y ⟨hyA, a, haA, rfl⟩
      change p * a * p⁻¹ ∈ A at hyA
      have hdA : ⁅p, a⁆ ∈ A := mul_mem hyA (inv_mem haA)
      have hdP : ⁅p, a⁆ ∈ P := by
        rw [← commutatorElement_inv]
        exact P.inv_mem (displacement_core h a p (hAM haA) hp)
      have hdW : ⁅p, a⁆ ∈ W := hAP ▸ (show ⁅p, a⁆ ∈ A ⊓ P from ⟨hdA, hdP⟩)
      have hd2 : ⁅a, p⁆ ^ 2 = 1 := by
        rw [← commutatorElement_inv, inv_pow,
          elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hdA, inv_one]
      have hap : a ∈ P := by
        by_contra haP
        have hc : Commute a (p ^ 2) := commutatorElement_eq_one_iff_commute.mp
          ((displacement_square h a p (hAM haA) hp).symm.trans hd2)
        exact hpW ((fixed_seed h W hWV hW4 a (hAC haA) haP _ (core_square_seed h p hp)).mp hc)
      have haW : a ∈ W := hAP ▸ (show a ∈ A ⊓ P from ⟨haA, hap⟩)
      change p * a * p⁻¹ ∈ W
      rwa [show p * a = a * p from setLike_mul_comm hp hap, mul_inv_cancel_right]
    · exact le_inf hWA hWB
  refine ⟨hpair, commutator_le.mpr ?_⟩
  rintro a ha b ⟨b₀, hb₀, rfl⟩
  let d := ⁅p, b₀⁆
  have hdP : d ∈ P := by
    dsimp [d]
    rw [← commutatorElement_inv]
    exact P.inv_mem (displacement_core h b₀ p (hAM hb₀) hp)
  have hdW : d ^ 2 ∈ W := by
    dsimp [d]
    rw [← commutatorElement_inv, inv_pow, displacement_square h b₀ p (hAM hb₀) hp]
    apply W.inv_mem
    exact plane_displacement h W hWV hW4 b₀ (p ^ 2) (hAC hb₀)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) b₀ hb₀) (pow_mem hp 2)
      (by
        let := h.elementary
        rw [elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (core_square_seed h p hp)]
        exact one_mem _)
  have had := plane_displacement h W hWV hW4 a d (hAC ha)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) hdP hdW
  have he : (MulAut.conj p).toMonoidHom b₀ = d * b₀ := by
    simp only [d, commutatorElement_def, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
      mul_assoc, inv_mul_cancel, mul_one]
  rw [he, commutatorElement_mul_right_eq_mul_conj,
    (show Commute a b₀ from setLike_mul_comm ha hb₀).commutator_eq,
    mul_one, mul_inv_cancel_right] 
  exact had

/-- The original plane construction can be chosen pure while retaining
its literal plane and its intersection with the whole cyclic-four core. -/
theorem TypeAt.exists_pure_plane_sixteen (h : TypeAt z V) :
    ∃ W A : Subgroup G, W ≤ V ∧ Nat.card W = 4 ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ W ≤ A ∧
      A ≤ centralizer (W : Set G) ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) := by
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
  refine ⟨W, A, hWV, hW4, hAE, hA16, hWA, hAC, hAP, hCA, ?_⟩
  intro x hx hx1
  by_cases hxE : x ∈ E.val
  · exact (huT.centralizer_core_involution_isConj x (hDQ hxE)
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hx1)).trans
        (hseedpure u (hWV huW) hu1)
  · obtain ⟨q, _, hq⟩ := huT.nonseed_extension_exterior_transitive E hEn A hA16 hDA b hbA hbE x hx hxE
    exact (isConj_iff.mpr ⟨q, hq⟩).symm.trans hbz

/-- Original HS data construct two pure elementary-sixteen radicals whose
literal intersection is the original seed plane and whose join has order64.
The second is conjugate by an actual element of the whole cyclic-four core. -/
theorem TypeAt.exists_paired_plane_radicals (h : TypeAt z V) :
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
      (∀ x ∈ B, x ≠ 1 → IsConj x z) := by
  obtain ⟨W, A, hWV, hW4, hAE, hA16, hWA, hAC, hAP, hCA, hpure⟩ :=
    h.exists_pure_plane_sixteen
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
  refine ⟨W, A, B, p, hWV, hW4, hAE, hA16, hBE, hB16, hp, hpW, rfl,
    hAP, hBP, hCA, hCB, hi, hc, hAB, hBA, h64, sup_le hAC hBC, hpure, ?_⟩
  rintro x ⟨a, ha, rfl⟩ hx1
  have ha1 : a ≠ 1 := fun ha1 => hx1 (by simp only [ha1, map_one])
  exact (isConj_iff.mpr ⟨p, rfl⟩).symm.trans (hpure a ha ha1)

end CFSG.Quasithin.HigmanSims
