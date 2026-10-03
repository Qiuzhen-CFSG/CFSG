module

public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.IndexNormal

/-!
# Elementary centralizers in index-two extraspecial extensions

The center of a normal extraspecial two-subgroup is central in the overgroup.
The core part of the centralizer of an outside involution contains this center,
so it is normal in the core. The outside involution centralizes it, proving
normality in the whole index-two extension. If this centralizer is elementary,
the absence of normal elementary eights bounds its core part by four.

Source: Janko–Thompson (1970), §4, printed p.389, the index-two paragraph.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

/-- The core centralizer of an outside involution is normal in an index-two
extraspecial extension. -/
public theorem extraspecial_inf_centralizer_normal_of_index_two
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [IsExtraspecial 2 H] (hi : H.index = 2)
    (t : P) (ht : t ^ 2 = 1) (hout : t ∉ H) :
    (H ⊓ centralizer ({t} : Set P) : Subgroup P).Normal := by
  let : H.Normal := H.normal_of_index_eq_two hi
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZ : Z ≤ center P := central_of_normal_card_two Z
    ((card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H))
  let F := H ⊓ centralizer ({t} : Set P)
  let K := F.subgroupOf H
  have hZK : center H ≤ K := by
    intro x hx
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mem_center_iff.mp (hZ (mem_map_of_mem H.subtype hx)) t).symm
  have hKn : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_top le_top).trans
      ((IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient.trans hZK)
  let : K.Normal := hKn
  have hKF : K.map H.subtype = F := map_subgroupOf_eq_of_le inf_le_left
  have hHN : H ≤ normalizer (F : Set P) := by
    have hh := K.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype, hKF] using hh
  have htC : t ∈ centralizer (F : Set P) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2
  have hgen : H ⊔ zpowers t = ⊤ := by
    apply eq_top_of_card_eq
    rw [card_sup_zpowers_of_normalizing_involution H t ht hout
      (show t ∈ normalizer (H : Set P) by rw [H.normalizer_eq_top]; trivial)]
    have hh := H.card_mul_index
    rw [hi] at hh
    omega
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le hHN (zpowers_le.mpr (centralizer_le_normalizer _ htC))

/-- An elementary centralizer with core part of order at least four has
core part of order four, and total order eight, under the normal-only bound. -/
public theorem extraspecial_index_two_elementary_centralizer_card
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (H : Subgroup P) [IsExtraspecial 2 H] (hi : H.index = 2)
    (t : P) (ht : t ^ 2 = 1) (hout : t ∉ H)
    [IsElementaryAbelian 2 (centralizer ({t} : Set P))]
    (hfixed : 4 ≤ Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P)) :
    Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 4 ∧
      centralizer ({t} : Set P) =
        (H ⊓ centralizer ({t} : Set P)) ⊔ zpowers t ∧
      Nat.card (centralizer ({t} : Set P)) = 8 := by
  let C := centralizer ({t} : Set P)
  let F := H ⊓ C
  let : F.Normal := extraspecial_inf_centralizer_normal_of_index_two H hi t ht hout
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro a b
      exact Subtype.ext (congrArg (fun x : C => (x : P))
        (mul_comm (⟨a, a.property.2⟩ : C) (⟨b, b.property.2⟩ : C))))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := C) a a.property.2)) }
  change 4 ≤ Nat.card F at hfixed
  have hsmall : Nat.card F < 8 := by
    by_contra! hlarge
    exact hno ⟨F, inferInstance, inferInstance, hlarge⟩
  have hF : Nat.card F = 4 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 F).exists_card_eq
    have hnlt : n < 3 := by
      by_contra! h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) h
      rw [← hn] at hh
      norm_num at hh
      omega
    interval_cases n <;> norm_num only [pow_zero, pow_one, Nat.reducePow] at hn <;> omega
  have htc : t ∈ C := mem_centralizer_singleton_iff.mpr (Commute.refl t)
  have htF : t ∈ centralizer (F : Set P) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2
  have hsplit : C = F ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      by_cases hxH : x ∈ H
      · exact (le_sup_left : F ≤ F ⊔ zpowers t) ⟨hxH, hx⟩
      · have htxH : t * x ∈ H :=
          (mul_mem_iff_of_index_two hi).mpr (iff_of_false hout hxH)
        have htxF : t * x ∈ F := ⟨htxH, C.mul_mem htc hx⟩
        have hh := (F ⊔ zpowers t).mul_mem
          ((le_sup_right : zpowers t ≤ F ⊔ zpowers t) (mem_zpowers t))
          ((le_sup_left : F ≤ F ⊔ zpowers t) htxF)
        simpa only [← mul_assoc, ← pow_two, ht, one_mul] using hh
    · exact sup_le inf_le_right (zpowers_le.mpr htc)
  refine ⟨hF, hsplit, ?_⟩
  change Nat.card C = 8
  rw [hsplit, card_sup_zpowers_of_normalizing_involution F t ht
    (fun h => hout h.1) (centralizer_le_normalizer _ htF), hF]

end Subgroup
