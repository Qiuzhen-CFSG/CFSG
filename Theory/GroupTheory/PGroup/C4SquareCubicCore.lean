module

public import Theory.GroupTheory.PGroup.C4SquareCubicOutsideGeometry

/-!
# Central commutator calculations in the cubic core

The core has all squares in the ambient central omega four, so its
commutators lie there as well. A non-base core element has fixed subgroup
exactly that four-group on the base. Its commutator row on the base is
therefore onto the four-group, and its core centralizer has order sixteen.

An outside element with fourth power one is an involution. Applying this
observation to an element centralizing a non-base core element excludes
outside centralizers entirely. These facts do not require the split/Higman
dichotomy or an elementary-rank bound.

Source: MacWilliams, Trans. AMS 150 (1970), Lemma 3 and the calculations
following (xxii), printed pp.380–384, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace C4SquareCubicInvertingExtension
variable {P : Type*} [Group P] [Finite P]
  {C R : Subgroup P} {a : MulAut P} {t : P}
  (h : C4SquareCubicInvertingExtension C R a t)
  (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
  (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
  (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
  (e : C ≃* C4SquareExtension.Model)

include hC hno hZ in
omit [IsMulCommutative C] in
/-- The ambient central omega four lies in the critical base. -/
public theorem omega_le_base :
    (omega₁ (center P) (p := 2)).map (center P).subtype ≤ C := by
  rw [← hC.omega_one_map_eq_center hno hZ]
  exact map_subtype_le _

include h hC hno hZ e in
/-- Every commutator of core elements lies in the central omega four. -/
public theorem core_commutator_mem_omega (x y : P) (hx : x ∈ R) (hy : y ∈ R) :
    ⁅x, y⁆ ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  let W := (omega₁ (center P) (p := 2)).map (center P).subtype
  let : W.Normal := ⟨fun w hw g => by
    rw [(mem_center_iff.mp (map_subtype_le _ hw)) g, mul_inv_cancel_right]
    exact hw⟩
  let q := QuotientGroup.mk' W
  have hs (r : P) (hr : r ∈ R) : q r ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (h.core_square_mem_omega hC hno hZ e r hr)
  have hi (r : P) (hr : r ∈ R) : (q r)⁻¹ = q r :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs r hr)
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅x, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  calc
    q x * q y = q (x * y) := (map_mul q x y).symm
    _ = (q (x * y))⁻¹ := (hi _ (R.mul_mem hx hy)).symm
    _ = q y * q x := by rw [map_mul, mul_inv_rev, hi y hy, hi x hx]

include h hC hno hZ e in
/-- Every core subgroup containing the central omega is normal in the core. -/
public theorem core_le_normalizer_of_omega_le (E : Subgroup P) (hER : E ≤ R)
    (hWE : (omega₁ (center P) (p := 2)).map (center P).subtype ≤ E) :
    R ≤ normalizer (E : Set P) := by
  intro r hr
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    have hm := E.mul_mem (hWE (h.core_commutator_mem_omega hC hno hZ e r x hr (hER hx))) hx
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
  · intro hx
    have hm := E.mul_mem (hWE (h.core_commutator_mem_omega hC hno hZ e r⁻¹
      (r * x * r⁻¹) (R.inv_mem hr) (hER hx))) hx
    simpa only [commutatorElement_def, mul_assoc, inv_inv, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, mul_inv_cancel_right] using hm

include h hC hno hZ e in
/-- Outside elements of order dividing four are involutions or the identity. -/
public theorem outside_square_eq_one_of_fourth_eq_one (x : P) (hxR : x ∉ R)
    (hx4 : x ^ 4 = 1) : x ^ 2 = 1 := by
  let r := x * t
  have hr : r ∈ R := (R.mul_mem_iff_of_index_two h.core_index).mpr
    (iff_of_false hxR h.outside_not_mem)
  have ht2 : t * t = 1 := by simpa only [pow_two] using
    (show t ^ 2 = 1 from h.outside_order ▸ pow_orderOf_eq_one t)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hx : x = r * t := by dsimp only [r]; rw [mul_assoc, ht2, mul_one]
  have hrC : r ∈ C := by
    by_contra hn
    have hr2 := h.core_square_mem_omega hC hno hZ e r hr
    have hz : r ^ 2 ∈ center P := map_subtype_le _ hr2
    have hi : Commute (r ^ 2) (x ^ 2) :=
      (show Commute (r ^ 2) x from ((mem_center_iff.mp hz) x).symm).pow_right 2
    have hr4 : (r ^ 2) ^ 2 = 1 := by
      let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative _
      let : IsElementaryAbelian 2 ((omega₁ (center P) (p := 2)).map (center P).subtype) :=
        IsElementaryAbelian.map_subtype
      exact elemPow_eq_one_of_isElementaryAbelian _ hr2
    apply h.mixed_commutator r hr hn
    have heq : r * t * r⁻¹ * t⁻¹ = (r ^ 2)⁻¹ * x ^ 2 := by
      have hr2t : t * r ^ 2 = r ^ 2 * t := (mem_center_iff.mp hz) t
      rw [hx, hti]
      calc
        r * t * r⁻¹ * t = r⁻¹ * (r ^ 2 * t) * r⁻¹ * t := by group
        _ = r⁻¹ * (t * r ^ 2) * r⁻¹ * t := by rw [hr2t]
        _ = (r ^ 2)⁻¹ * (r * t) ^ 2 := by simp only [pow_two]; group
    rw [heq, hi.inv_left.mul_pow, inv_pow, hr4, inv_one, one_mul, ← pow_mul]
    exact hx4
  rw [hx, pow_two]
  calc
    r * t * (r * t) = r * (t * r * t⁻¹) := by rw [hti]; group
    _ = r * r⁻¹ := by rw [h.outside_inverts r hrC]
    _ = 1 := mul_inv_cancel r

include h hC hno hZ e in
/-- The ambient centralizer of a non-base core element lies in the core. -/
public theorem inside_centralizer_le_core (u : P) (huR : u ∈ R) (huC : u ∉ C) : centralizer ({u} : Set P) ≤ R := by
  intro x hx
  by_contra hxR
  have hxC := hC.square_mem_of_c4_square hno hZ e x
  have hxu : Commute x u := mem_centralizer_singleton_iff.mp hx
  have hx4 : x ^ 4 = 1 := by
    simpa only [← pow_mul] using h.core_fixed_elements u huR huC (x ^ 2) hxC
      (hxu.pow_left 2)
  have hx2 := h.outside_square_eq_one_of_fourth_eq_one hC hno hZ e x hxR hx4
  have hxo : orderOf x = 2 := orderOf_eq_prime (by simpa only [pow_two] using hx2)
    (by intro hx1; exact hxR (hx1 ▸ R.one_mem))
  have huW : u ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
    rw [← h.outside_centralizer_inf_core hC hno hZ e x hxR hxo]
    exact ⟨mem_centralizer_singleton_iff.mpr hxu.symm.eq, huR⟩
  exact huC (omega_le_base hC hno hZ huW)

include h hC hno hZ in
omit [IsMulCommutative C] in
/-- A non-base core element centralizes exactly the central omega in the base. -/
public theorem core_centralizer_inf_base (u : P) (huR : u ∈ R) (huC : u ∉ C) :
    centralizer ({u} : Set P) ⊓ C =
      (omega₁ (center P) (p := 2)).map (center P).subtype := by
  apply le_antisymm
  · intro c hc
    exact hC.mem_omega_center_of_square_eq_one hno hZ hc.2
      (h.core_fixed_elements u huR huC c hc.2
        (mem_centralizer_singleton_iff.mp hc.1))
  · intro w hw
    exact ⟨center_le_centralizer _ (map_subtype_le _ hw), omega_le_base hC hno hZ hw⟩

private def coreCommutatorRow (K : Subgroup P) (hKR : K ≤ R)
    (u : P) (huR : u ∈ R) :
    K →* (omega₁ (center P) (p := 2)).map (center P).subtype where
  toFun x := ⟨⁅u, (x : P)⁆, h.core_commutator_mem_omega hC hno hZ e u x huR (hKR x.property)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change ⁅u, (x : P) * (y : P)⁆ = ⁅u, (x : P)⁆ * ⁅u, (y : P)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hz : ⁅u, (y : P)⁆ ∈ center P := map_subtype_le _
      (h.core_commutator_mem_omega hC hno hZ e u y huR (hKR y.property))
    calc
      _ = ⁅u, (x : P)⁆ * ((x : P) * ⁅u, (y : P)⁆) * (x : P)⁻¹ := by group
      _ = ⁅u, (x : P)⁆ * ⁅u, (y : P)⁆ := by
        rw [(mem_center_iff.mp hz) x]; group

private theorem coreCommutatorRow_ker (K : Subgroup P) (hKR : K ≤ R)
    (u : P) (huR : u ∈ R) :
    (coreCommutatorRow h hC hno hZ e K hKR u huR).ker =
      (centralizer ({u} : Set P)).subgroupOf K := by
  ext x
  change (⟨⁅u, (x : P)⁆, _⟩ : (omega₁ (center P) (p := 2)).map (center P).subtype) = 1 ↔ _
  rw [Subtype.ext_iff]
  change ⁅u, (x : P)⁆ = 1 ↔ (x : P) ∈ centralizer ({u} : Set P)
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
  exact eq_comm

include h hC hno hZ e in
/-- The commutator row of a non-base core element maps the base onto the central omega. -/
public theorem exists_base_commutator (u : P) (huR : u ∈ R) (huC : u ∉ C)
    (w : P) (hw : w ∈ (omega₁ (center P) (p := 2)).map (center P).subtype) :
    ∃ c ∈ C, ⁅u, c⁆ = w := by
  let f := coreCommutatorRow h hC hno hZ e C h.base_le u huR
  have hk : Nat.card f.ker = 4 := by
    rw [coreCommutatorRow_ker,
      ← card_map_of_injective (K := (centralizer ({u} : Set P)).subgroupOf C) C.subtype_injective,
      subgroupOf_map_subtype, h.core_centralizer_inf_base hC hno hZ u huR huC,
      card_map_of_injective (center P).subtype_injective, hZ]
  have hc : Nat.card C = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]; norm_num
  have hs : Function.Surjective f := f.surjective_of_card_ker_le_div (by
    rw [hk, hc, card_map_of_injective (center P).subtype_injective, hZ])
  obtain ⟨c, hc⟩ := hs ⟨w, hw⟩
  exact ⟨c, c.property, congrArg Subtype.val hc⟩

include h hC hno hZ e in
/-- Every non-base core element has ambient centralizer of order sixteen. -/
public theorem inside_centralizer_card (u : P) (huR : u ∈ R) (huC : u ∉ C) :
    Nat.card (centralizer ({u} : Set P)) = 16 := by
  let f := coreCommutatorRow h hC hno hZ e R le_rfl u huR
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨c, hc, he⟩ := h.exists_base_commutator hC hno hZ e u huR huC w w.property
    exact ⟨⟨c, h.base_le hc⟩, Subtype.ext he⟩
  have hk : Nat.card f.ker = Nat.card (centralizer ({u} : Set P)) := by
    rw [coreCommutatorRow_ker,
      ← card_map_of_injective (K := (centralizer ({u} : Set P)).subgroupOf R) R.subtype_injective,
      subgroupOf_map_subtype, inf_eq_left.mpr (h.inside_centralizer_le_core hC hno hZ e u huR huC)]
  have hm := f.ker.index_mul_card
  rw [index_ker, MonoidHom.range_eq_top.mpr hs, card_top,
    card_map_of_injective (center P).subtype_injective, hZ, hk, h.core_card] at hm
  omega

/-- The split core's square-one elements lie in two elementary sixteens,
intersecting in the ambient central omega four. -/
public structure SplitInvolutionCover {P : Type*} [Group P] (R X Y : Subgroup P) : Prop where
  left_le : X ≤ R
  right_le : Y ≤ R
  left_elementary : IsElementaryAbelian 2 X
  right_elementary : IsElementaryAbelian 2 Y
  left_card : Nat.card X = 16
  right_card : Nat.card Y = 16
  inf_eq : X ⊓ Y = (omega₁ (center P) (p := 2)).map (center P).subtype
  cover : ∀ u ∈ R, u ^ 2 = 1 → u ∈ X ∨ u ∈ Y

/-- The two elementary sixteens may be interchanged. -/
public theorem SplitInvolutionCover.symm {P : Type*} [Group P] {R X Y : Subgroup P}
    (s : SplitInvolutionCover R X Y) : SplitInvolutionCover R Y X where
  left_le := s.right_le
  right_le := s.left_le
  left_elementary := s.right_elementary
  right_elementary := s.left_elementary
  left_card := s.right_card
  right_card := s.left_card
  inf_eq := (inf_comm _ _).trans s.inf_eq
  cover u hu hu2 := (s.cover u hu hu2).symm

/-- Every elementary subgroup in the core lies in one member of the cover. -/
public theorem SplitInvolutionCover.elementary_le_left_or_right {P : Type*} [Group P]
    {R X Y : Subgroup P} (s : SplitInvolutionCover R X Y)
    (E : Subgroup P) (hE : IsElementaryAbelian 2 E) (hER : E ≤ R) : E ≤ X ∨ E ≤ Y := by
  let : IsElementaryAbelian 2 E := hE
  apply SubgroupClass.subset_union.mp
  intro u hu
  exact s.cover u (hER hu) (elemPow_eq_one_of_isElementaryAbelian u hu)

include h hC hno hZ e in
/-- An elementary sixteen containing a non-base core element is its full centralizer. -/
public theorem centralizer_eq_of_elementary_sixteen (A : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (u : P) (huA : u ∈ A) (huR : u ∈ R) (huC : u ∉ C) :
    centralizer ({u} : Set P) = A := by
  let : IsElementaryAbelian 2 A := hA
  have hle : A ≤ centralizer ({u} : Set P) :=
    A.le_centralizer.trans (centralizer_le (Set.singleton_subset_iff.mpr huA))
  exact (eq_of_le_of_card_ge hle (by rw [hcard, h.inside_centralizer_card hC hno hZ e u huR huC])).symm

include h hC hno hZ e in
/-- A split involution cover supplies the inside centralizer profile. -/
public theorem inside_centralizer_profile_of_split {X Y : Subgroup P} (s : SplitInvolutionCover R X Y)
    (u : P) (huR : u ∈ R) (hu2 : orderOf u = 2) :
    u ∈ center P ∨ (IsElementaryAbelian 2 (centralizer ({u} : Set P)) ∧
      Nat.card (centralizer ({u} : Set P)) = 16) := by
  by_cases huC : u ∈ C
  · exact Or.inl (hC.involution_mem_ambient_center hno hZ huC hu2)
  · right
    rcases s.cover u huR (hu2 ▸ pow_orderOf_eq_one u) with huX | huY
    · rw [h.centralizer_eq_of_elementary_sixteen hC hno hZ e X s.left_elementary
        s.left_card u huX huR huC]
      exact ⟨s.left_elementary, s.left_card⟩
    · rw [h.centralizer_eq_of_elementary_sixteen hC hno hZ e Y s.right_elementary
        s.right_card u huY huR huC]
      exact ⟨s.right_elementary, s.right_card⟩

include h hno in
omit [Finite P] [IsMulCommutative C] in
/-- An elementary sixteen normalized by the core has normalizer exactly the core. -/
public theorem normalizer_elementary_sixteen_eq_core (A : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (hRN : R ≤ normalizer (A : Set P)) : normalizer (A : Set P) = R := by
  apply le_antisymm _ hRN
  intro x hx
  by_contra hxR
  have htop : normalizer (A : Set P) = ⊤ := by
    apply top_unique
    intro y _
    by_cases hyR : y ∈ R
    · exact hRN hyR
    · have hyx : y * x⁻¹ ∈ R := (R.mul_mem_iff_of_index_two h.core_index).mpr
        (iff_of_false hyR (by simpa only [inv_mem_iff] using hxR))
      have hm := (normalizer (A : Set P)).mul_mem (hRN hyx) hx
      simpa only [inv_mul_cancel_right] using hm
  exact hno ⟨A, normalizer_eq_top_iff.mp htop, hA, by omega⟩

end C4SquareCubicInvertingExtension
