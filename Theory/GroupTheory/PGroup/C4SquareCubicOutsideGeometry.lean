module

public import Theory.GroupTheory.PGroup.C4SquareCubicExtension
public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.ElementaryEightIndexTwoGeometry
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# Outside involutions in a cubic C₄-square extension

The mixed-commutator identity excludes involutions from the three mixed
core cosets. The distinguished elementary eight has normalizer of order 32,
whose intersection with the core is the C₄-square base. An elementary
subgroup of that normalizer has order at most eight. Every outside involution
centralizes exactly the central omega inside the core, and therefore has
centralizer of order eight. Counting its conjugates shows that all outside
involutions form one conjugacy class; thus every elementary eight meeting
the outside coset has the distinguished normalizer profile.

These calculations use the supplied algebraic extension without classifying
the core as split or of G. Higman type. The final assembly leaves only the
inside centralizers and the elementary-eight normalizer alternatives explicit.

Source: MacWilliams, Trans. AMS 150 (1970), Case 1.2, printed pp.382–384,
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
open scoped IsMulCommutative
namespace C4SquareCubicInvertingExtension
variable {P : Type*} [Group P] [Finite P]
  {C R : Subgroup P} {a : MulAut P} {t : P}
  (h : C4SquareCubicInvertingExtension C R a t)
  (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
  (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
  (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
  (e : C ≃* C4SquareExtension.Model)

include e in
omit [Finite P] [IsMulCommutative C] in
private theorem base_fourth (c : P) (hc : c ∈ C) : c ^ 4 = 1 := by
  have hh : (⟨c, hc⟩ : C) ^ 4 = 1 := e.injective (by
    rw [map_pow, map_one]
    exact (by decide : ∀ x : C4SquareExtension.Model, x ^ 4 = 1) _)
  exact congrArg Subtype.val hh

include h hC hno hZ e

/-- All squares in the core lie in the central omega four. -/
public theorem core_square_mem_omega (r : P) (hr : r ∈ R) :
    r ^ 2 ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  have hs := hC.square_mem_of_c4_square hno hZ e r
  apply hC.mem_omega_center_of_square_eq_one hno hZ hs
  by_cases hrC : r ∈ C
  · simpa only [← pow_mul] using base_fourth e r hrC
  · exact h.core_fixed_elements r hr hrC _ hs ((Commute.refl r).pow_left 2)

/-- An outside involution belongs to the coset of the base represented by t. -/
public theorem outside_involution_mul_mem_base
    (u : P) (huR : u ∉ R) (hu2 : orderOf u = 2) : u * t ∈ C := by
  let r := u * t
  have hrR : r ∈ R := (R.mul_mem_iff_of_index_two h.core_index).mpr
    (iff_of_false huR h.outside_not_mem)
  by_contra hrC
  have ht2 : t * t = 1 := by simpa only [pow_two] using
    (show t ^ 2 = 1 from h.outside_order ▸ pow_orderOf_eq_one t)
  have hu2' : u * u = 1 := by simpa only [pow_two] using
    (show u ^ 2 = 1 from hu2 ▸ pow_orderOf_eq_one u)
  have hiu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
  have hit : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have heq : r * t * r⁻¹ * t⁻¹ = r ^ 2 := by
    dsimp only [r]
    simp only [mul_inv_rev, hiu, hit, pow_two]
    simp only [mul_assoc, ht2, mul_one]
  have hr2C := hC.square_mem_of_c4_square hno hZ e r
  have hc : Commute (r ^ 2) r := (Commute.refl r).pow_left 2
  exact h.mixed_commutator r hrR hrC (heq ▸ h.core_fixed_elements r hrR hrC
    (r ^ 2) hr2C hc)

omit [IsMulCommutative C] in
/-- The base normalizes the distinguished elementary centralizer. -/
public theorem base_le_normalizer_centralizer :
    C ≤ normalizer (centralizer ({t} : Set P) : Set P) := by
  let W := (omega₁ (center P) (p := 2)).map (center P).subtype
  let E := centralizer ({t} : Set P)
  have hE : E = W ⊔ zpowers t := h.centralizer_eq_omega_sup hC hno hZ
  have htE : t ∈ E := mem_centralizer_singleton_iff.mpr rfl
  intro c hc
  have hc2W : c ^ 2 ∈ W := hC.mem_omega_center_of_square_eq_one hno hZ
    (C.pow_mem hc 2) (by simpa only [← pow_mul] using base_fourth e c hc)
  have hct : c * t * c⁻¹ = c ^ 2 * t := by
    have hh := h.outside_inverts c hc
    have hh' : t * c⁻¹ * t⁻¹ = c := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hh
    calc
      c * t * c⁻¹ = c * (t * c⁻¹ * t⁻¹) * t := by group
      _ = c ^ 2 * t := by rw [hh', pow_two]
  have hctE : c * t * c⁻¹ ∈ E := by
    rw [hct]
    exact E.mul_mem ((show W ≤ E from hE ▸ le_sup_left) hc2W) htE
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · change E.map (MulAut.conj c).toMonoidHom ≤ E
    rw [hE, Subgroup.map_sup, MonoidHom.map_zpowers]
    apply sup_le
    · rintro x ⟨w, hw, rfl⟩
      have hz := map_subtype_le _ hw
      have heq : c * w * c⁻¹ = w := by
        rw [(mem_center_iff.mp hz) c, mul_assoc, mul_inv_cancel, mul_one]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, heq] using
        ((show W ≤ W ⊔ zpowers t from le_sup_left) hw)
    · exact zpowers_le.mpr (hE ▸ hctE)
  · rw [card_map_of_injective (MulAut.conj c).injective]

omit [IsMulCommutative C] in
/-- Inside the core, exactly the base normalizes the distinguished eight. -/
public theorem normalizer_inf_core_eq_base :
    normalizer (centralizer ({t} : Set P) : Set P) ⊓ R = C := by
  let E := centralizer ({t} : Set P)
  let : IsElementaryAbelian 2 E := (h.centralizer_elementary_and_card hC hno hZ).1
  apply le_antisymm
  · intro r hr
    by_contra hrC
    apply h.mixed_commutator r hr.2 hrC
    have htE : t ∈ E := mem_centralizer_singleton_iff.mpr rfl
    have hm : r * t * r⁻¹ * t⁻¹ ∈ E :=
      E.mul_mem ((hr.1 t).mp htE) (E.inv_mem htE)
    exact elemPow_eq_one_of_isElementaryAbelian _ hm
  · exact le_inf (h.base_le_normalizer_centralizer hC hno hZ e) h.base_le

omit [IsMulCommutative C] in
/-- The distinguished normalizer has order 32. -/
public theorem normalizer_centralizer_card :
    Nat.card (normalizer (centralizer ({t} : Set P) : Set P)) = 32 := by
  let N := normalizer (centralizer ({t} : Set P) : Set P)
  have htN : t ∈ N := (centralizer ({t} : Set P)).le_normalizer
    (mem_centralizer_singleton_iff.mpr rfl)
  have hi : (R.subgroupOf N).index = 2 :=
    subgroupOf_index_eq_two R N h.core_index (fun hn => h.outside_not_mem (hn htN))
  have hc : Nat.card (R.subgroupOf N) = 16 := by
    rw [← card_map_of_injective (K := R.subgroupOf N) N.subtype_injective,
      subgroupOf_map_subtype, inf_comm R N, h.normalizer_inf_core_eq_base hC hno hZ e,
      Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hm := (R.subgroupOf N).card_mul_index
  rw [hi, hc] at hm
  exact hm.symm

omit [IsMulCommutative C] in
/-- No elementary subgroup of the distinguished normalizer has order sixteen. -/
public theorem normalizer_centralizer_no_sixteen
    (A : Subgroup (normalizer (centralizer ({t} : Set P) : Set P)))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≠ 16 := by
  let N := normalizer (centralizer ({t} : Set P) : Set P)
  let B := A.map N.subtype
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : C.Characteristic := hC.characteristic
  let W := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hi : B ⊓ C ≤ W := by
    intro x hx
    exact hC.mem_omega_center_of_square_eq_one hno hZ hx.2
      (elemPow_eq_one_of_isElementaryAbelian x hx.1)
  have hiC : Nat.card (B ⊓ C : Subgroup P) ≤ 4 := by
    have hh := card_le_of_le hi
    simpa only [W, card_map_of_injective (center P).subtype_injective, hZ] using hh
  have hs : B ⊔ C ≤ N := sup_le (map_subtype_le _)
    (h.base_le_normalizer_centralizer hC hno hZ e)
  have hsC : Nat.card (B ⊔ C : Subgroup P) ≤ 32 := by
    have hh := card_le_of_le hs
    rwa [h.normalizer_centralizer_card hC hno hZ e] at hh
  have hCcard : Nat.card C = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B
    (show B ≤ normalizer (C : Set P) from le_normalizer_of_normal)
  rw [inf_comm C B, sup_comm C B, hCcard] at hm
  intro hcA
  have hB : Nat.card B = 16 := by
    rw [card_map_of_injective N.subtype_injective, hcA]
  rw [hB] at hm
  nlinarith [Nat.mul_le_mul hiC hsC]

/-- Every outside involution centralizes just the central omega inside the core. -/
public theorem outside_centralizer_inf_core
    (u : P) (huR : u ∉ R) (hu2 : orderOf u = 2) :
    centralizer ({u} : Set P) ⊓ R =
      (omega₁ (center P) (p := 2)).map (center P).subtype := by
  let : C.Characteristic := hC.characteristic
  let c := u * t
  have hc : c ∈ C := h.outside_involution_mul_mem_base hC hno hZ e u huR hu2
  have ht2 : t * t = 1 := by
    simpa only [pow_two] using (show t ^ 2 = 1 from h.outside_order ▸ pow_orderOf_eq_one t)
  have hu : u = c * t := by dsimp only [c]; rw [mul_assoc, ht2, mul_one]
  have hc2Z : c ^ 2 ∈ center P := map_subtype_le _
    (hC.mem_omega_center_of_square_eq_one hno hZ (C.pow_mem hc 2)
      (by simpa only [← pow_mul] using base_fourth e c hc))
  apply le_antisymm
  · intro r hr
    have hru : r * u = u * r := mem_centralizer_singleton_iff.mp hr.1
    have hrC : r ∈ C := by
      by_contra hrC
      apply h.mixed_commutator r hr.2 hrC
      let d := r * c * r⁻¹
      have hdC : d ∈ C := (inferInstance : C.Normal).conj_mem c hc r
      have hdc : Commute d c := by
        exact congrArg Subtype.val
          (show (⟨d, hdC⟩ : C) * ⟨c, hc⟩ = ⟨c, hc⟩ * ⟨d, hdC⟩ from
            (mul_comm _ _))
      have hd2 : d ^ 2 = c ^ 2 := by
        calc
          d ^ 2 = r * c ^ 2 * r⁻¹ := by dsimp only [d]; simp only [pow_two]; group
          _ = c ^ 2 := by
            rw [(mem_center_iff.mp hc2Z) r, mul_assoc, mul_inv_cancel, mul_one]
      have hdisp : r * t * r⁻¹ * t⁻¹ = d⁻¹ * c := by
        have hh : d * (r * t * r⁻¹ * t⁻¹) = c := by
          calc
            d * (r * t * r⁻¹ * t⁻¹) = r * u * r⁻¹ * t⁻¹ := by rw [hu]; dsimp only [d]; group
            _ = u * t⁻¹ := by rw [hru]; group
            _ = c := by rw [hu]; group
        exact (eq_inv_mul_iff_mul_eq).mpr hh
      rw [hdisp, hdc.inv_left.mul_pow, inv_pow, hd2, inv_mul_cancel]
    have hcu : u * r * u⁻¹ = r⁻¹ := by
      rw [hu, mul_inv_rev]
      calc
        c * t * r * (t⁻¹ * c⁻¹) = c * (t * r * t⁻¹) * c⁻¹ := by group
        _ = c * r⁻¹ * c⁻¹ := by rw [h.outside_inverts r hrC]
        _ = r⁻¹ := by
          have hcomm : Commute c r⁻¹ := congrArg Subtype.val
            (show (⟨c, hc⟩ : C) * (⟨r, hrC⟩ : C)⁻¹ =
              (⟨r, hrC⟩ : C)⁻¹ * ⟨c, hc⟩ from mul_comm _ _)
          exact hcomm.mul_inv_cancel
    have hir : r⁻¹ = r := by rw [← hcu, ← hru, mul_inv_cancel_right]
    exact hC.mem_omega_center_of_square_eq_one hno hZ hrC
      (by rw [pow_two]; nth_rw 1 [← hir]; exact inv_mul_cancel r)
  · intro w hw
    refine ⟨center_le_centralizer _ (map_subtype_le _ hw), ?_⟩
    apply h.base_le
    rw [← hC.omega_one_map_eq_center hno hZ] at hw
    exact map_subtype_le _ hw

/-- All outside involutions have centralizer of order eight. Counting its conjugates shows that all outside
involutions form one conjugacy class; thus every elementary eight meeting
the outside coset has the distinguished normalizer profile. -/
public theorem outside_centralizer_card
    (u : P) (huR : u ∉ R) (hu2 : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set P)) = 8 := by
  let U := centralizer ({u} : Set P)
  have huU : u ∈ U := mem_centralizer_singleton_iff.mpr rfl
  have hi : (R.subgroupOf U).index = 2 :=
    subgroupOf_index_eq_two R U h.core_index (fun hn => huR (hn huU))
  have hc : Nat.card (R.subgroupOf U) = 4 := by
    rw [← card_map_of_injective (K := R.subgroupOf U) U.subtype_injective,
      subgroupOf_map_subtype, inf_comm R U,
      h.outside_centralizer_inf_core hC hno hZ e u huR hu2,
      card_map_of_injective (center P).subtype_injective, hZ]
  have hm := (R.subgroupOf U).card_mul_index
  rw [hi, hc] at hm
  exact hm.symm

/-- The outside involutions form a single conjugacy class. -/
public theorem outside_isConj (u : P) (huR : u ∉ R) (hu2 : orderOf u = 2) : IsConj t u := by
  let : R.Normal := R.normal_of_index_eq_two h.core_index
  have props (x : P) (hx : IsConj t x) : x ∉ R ∧ orderOf x = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    refine ⟨?_, ((MulAut.conj g).orderOf_eq t).trans h.outside_order⟩
    intro hx
    have hh := (inferInstance : R.Normal).conj_mem _ hx g⁻¹
    simp only [inv_inv] at hh
    exact h.outside_not_mem (by simpa only [mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh)
  let X := {x : P // IsConj t x}
  let f : X → C := fun x => ⟨x * t,
    h.outside_involution_mul_mem_base hC hno hZ e x (props x x.property).1
      (props x x.property).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (mul_right_cancel (congrArg Subtype.val hxy))
  have hX : Nat.card X = 16 := by
    have hh := ConjClasses.nat_card_carrier_mul_card_centralizer t
    change Nat.card X * Nat.card (centralizer ({t} : Set P)) = Nat.card P at hh
    rw [(h.centralizer_elementary_and_card hC hno hZ).2, h.card_eq_128] at hh
    omega
  have hCcard : Nat.card C = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hsurj := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hX.trans hCcard.symm⟩
  obtain ⟨x, hx⟩ := hsurj.2 ⟨u * t,
    h.outside_involution_mul_mem_base hC hno hZ e u huR hu2⟩
  have heq : (x : P) = u := mul_right_cancel (congrArg Subtype.val hx)
  exact heq ▸ x.property

/-- Every elementary eight meeting the outside coset is conjugate to the distinguished one. -/
public theorem outside_elementary_eight_conjugate
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hout : ¬ E ≤ R) :
    ∃ g : P, (centralizer ({t} : Set P)).map (MulAut.conj g).toMonoidHom = E := by
  obtain ⟨u, huE, huR⟩ := SetLike.not_le_iff_exists.mp hout
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian u huE) (fun hh => huR (hh ▸ R.one_mem))
  have hEq : E = centralizer ({u} : Set P) := eq_of_le_of_card_ge
    (fun x hx => mem_centralizer_singleton_iff.mpr ((E.le_centralizer huE) x hx))
    (by rw [h.outside_centralizer_card hC hno hZ e u huR hu2, hE])
  obtain ⟨g, hg⟩ := isConj_iff.mp (h.outside_isConj hC hno hZ e u huR hu2)
  refine ⟨g, eq_of_le_of_card_ge ?_ ?_⟩
  · rw [hEq]
    have hh := map_centralizer_le_centralizer_image ({t} : Set P) (MulAut.conj g).toMonoidHom
    simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg] using hh
  · rw [card_map_of_injective (MulAut.conj g).injective,
      (h.centralizer_elementary_and_card hC hno hZ).2, hE]

/-- Every elementary eight outside the core has the first normalizer profile. -/
public theorem outside_elementary_eight_profile
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hout : ¬ E ≤ R) :
    centralizer (E : Set P) = E ∧ Nat.card (normalizer (E : Set P)) = 32 := by
  obtain ⟨u, huE, huR⟩ := SetLike.not_le_iff_exists.mp hout
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian u huE) (fun hh => huR (hh ▸ R.one_mem))
  have hEq : E = centralizer ({u} : Set P) := eq_of_le_of_card_ge
    (fun x hx => mem_centralizer_singleton_iff.mpr ((E.le_centralizer huE) x hx))
    (by rw [h.outside_centralizer_card hC hno hZ e u huR hu2, hE])
  refine ⟨le_antisymm ?_ E.le_centralizer, ?_⟩
  · exact (centralizer_le (Set.singleton_subset_iff.mpr huE)).trans hEq.ge
  · obtain ⟨g, hg⟩ := h.outside_elementary_eight_conjugate hC hno hZ e E hE hout
    rw [← hg, ← map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      card_map_of_injective (MulAut.conj g).injective]
    exact h.normalizer_centralizer_card hC hno hZ e

/-- The remaining core profiles complete the elementary-eight geometry.
Only elementary eights contained in the core need be supplied; the outside
profiles have already been proved. -/
public theorem geometry_of_core_profiles
    (hinside : ∀ u : P, u ∈ R → orderOf u = 2 →
      u ∈ center P ∨
        (IsElementaryAbelian 2 (centralizer ({u} : Set P)) ∧
          Nat.card (centralizer ({u} : Set P)) = 16))
    (hcases : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E = 8 → E ≤ R →
      (centralizer (E : Set P) = E ∧ Nat.card (normalizer (E : Set P)) = 32) ∨
      (Nat.card (normalizer (E : Set P)) = 64 ∧
        ∀ f : normalizer (centralizer ({t} : Set P) : Set P) →*
            normalizer (E : Set P), ¬ Function.Injective f) ∨
      (IsElementaryAbelian 2 (normalizer (E : Set P)) ∧
        Nat.card (normalizer (E : Set P)) = 16)) :
    ElementaryEightIndexTwoGeometry R t where
  index_eq_two := h.core_index
  order_eq_two := h.outside_order
  not_mem := h.outside_not_mem
  centralizer_elementary := (h.centralizer_elementary_and_card hC hno hZ).1
  centralizer_card := (h.centralizer_elementary_and_card hC hno hZ).2
  normalizer_card := h.normalizer_centralizer_card hC hno hZ e
  normalizer_no_sixteen := h.normalizer_centralizer_no_sixteen hC hno hZ e
  inside_centralizers := hinside
  outside_centralizers := h.outside_centralizer_card hC hno hZ e
  normalizer_cases := by
    intro E hE hcard
    by_cases hER : E ≤ R
    · exact hcases E hE hcard hER
    · let : IsElementaryAbelian 2 E := hE
      exact Or.inl (h.outside_elementary_eight_profile hC hno hZ e E hcard hER)

end C4SquareCubicInvertingExtension
