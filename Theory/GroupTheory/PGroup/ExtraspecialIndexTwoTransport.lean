module

public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo
public import Theory.GroupTheory.CharacteristicSylowCentralizerFusion
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion

/-!
# Transport into a unique normal four across an extraspecial index-two subgroup

Let a Sylow two-subgroup have an extraspecial subgroup of order thirty-two
and index two. Assume normal elementary eights are absent and the normal
four is unique. If the extraspecial subgroup is stable under conjugations
fixing a central involution, every distinct ambient conjugate of that
involution in the subgroup fuses to an element of the normal four.

A centralizer crossing the extraspecial subgroup has index two. Its two
central involutions generate a four, which the normal-only bound makes
normal. Otherwise its derived subgroup is the extraspecial center, so its
ambient normalizer fixes the central involution. The maximal-centralizer
argument then excludes a fused element whose class misses the normal four.
No elementary-rank bound or choice of extraspecial type is used.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389, the first
half of the paragraph beginning “Suppose |T:H|=2”.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsExtraspecial

/-- Every centralizer in an extraspecial group of order thirty-two has derived
image equal to the extraspecial center, for either extraspecial type. -/
public theorem centralizer_commutator_image_eq_center_of_card_thirty_two
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (hH : Nat.card H = 32) (t : H) :
    (_root_.commutator (centralizer ({t} : Set H))).map
      (centralizer ({t} : Set H)).subtype = center H := by
  let C := centralizer ({t} : Set H)
  have hC : 16 ≤ Nat.card C :=
    centralizer_card_ge_sixteen_of_card_thirty_two hH t
  have hci := C.card_mul_index
  rw [hH] at hci
  have hi : C.index ≤ 2 := by nlinarith
  have hnc : ¬ IsMulCommutative C := by
    intro hc
    by_cases htwo : C.index = 2
    · exact not_isMulCommutative_of_index_two (by omega) C htwo
        (center_le_centralizer _) hc
    · have htop : C = ⊤ := index_eq_one.mp (by
        have hp : C.index ≠ 0 := by intro h; simp [h] at hci
        omega)
      have hab : IsMulCommutative H := isMulCommutative_iff.mpr (by
        intro a b
        let : IsMulCommutative C := hc
        have ha : a ∈ C := htop ▸ mem_top a
        have hb : b ∈ C := htop ▸ mem_top b
        exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) (⟨b, hb⟩ : C)))
      let : Nontrivial (H ⧸ center H) := quotient_nontrivial 2 H
      exact QuotientGroup.nontrivial_iff.mp inferInstance (center_eq_top_iff.mpr hab)
  let D := (_root_.commutator C).map C.subtype
  have hle : D ≤ center H := by
    rw [show D = (_root_.commutator C).map C.subtype from rfl, map_subtype_commutator]
    exact (commutator_mono le_top le_top).trans
      (quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient
  have hne : D ≠ ⊥ := by
    intro h
    have hh : _root_.commutator C = ⊥ := map_injective C.subtype_injective
      (h.trans (Subgroup.map_bot _).symm)
    exact hnc ((commutator_eq_bot_iff C).mp hh)
  apply eq_of_le_of_card_ge hle
  rw [center_order_p 2 H]
  have hn : Nat.card D ≠ 1 := fun h => hne (card_eq_one.mp h)
  have hp := Nat.card_pos (α := D)
  omega

end IsExtraspecial

namespace Sylow

/-- A distinct involution with index-two centralizer lies in the unique normal
four, assuming only that normal elementary eights are absent. -/
public theorem mem_unique_normal_four_of_centralizer_index_two
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (ht : orderOf t = 2) (hne : t ≠ z)
    (hi : (centralizer ({t} : Set S)).index = 2) : t ∈ W := by
  let E := closure ({t, z} : Set S)
  let C := centralizer ({t} : Set S)
  let : IsKleinFour E := isKleinFour_closure_pair_of_orderOf t z ht hz hne
    (mem_center_iff.mp hzc t)
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let : C.Normal := normal_of_index_eq_two hi
  have hEC : E ≤ C := by
    apply (closure_le _).mpr
    intro x hx
    rcases (show x = t ∨ x = z from hx) with rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc t).symm
  have hCE : C ≤ centralizer (E : Set S) := by
    apply le_centralizer_iff.mp
    apply (closure_le _).mpr
    intro x hx
    rcases (show x = t ∨ x = z from hx) with rfl | rfl
    · intro c hc
      exact mem_centralizer_singleton_iff.mp hc
    · intro c _
      exact mem_center_iff.mp hzc c
  have heq : E = W := hunique E
    (normal_four_of_normal_centralizing_overgroup_of_no_normal_eight hno E C
      IsKleinFour.card_four hEC hCE) inferInstance IsKleinFour.card_four
  rw [← heq]
  exact subset_closure (by simp)

end Sylow

namespace Sylow

/-- Inside-core fusion transports into the unique normal four when the core
is stable under conjugations fixing the central involution. -/
public theorem exists_isConj_mem_unique_normal_four_of_extraspecial_index_two
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (H : Subgroup S) [IsExtraspecial 2 H] (hH : Nat.card H = 32) (hi : H.index = 2)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S) (hzH : z ∈ H)
    (hstable : ∀ t : S, t ∈ H → ∀ g : G, Commute g (z : G) →
      ∀ u : S, (MulAut.conj g) (t : G) = (u : G) → u ∈ H)
    (t : S) (htH : t ∈ H) (hconj : IsConj (z : G) (t : G)) (hne : t ≠ z) :
    ∃ u : S, u ∈ W ∧ u ≠ z ∧ IsConj (t : G) (u : G) := by
  classical
  let : H.Normal := normal_of_index_eq_two hi
  have hS : Nat.card S = 64 := by
    have hh := H.card_mul_index
    rw [hH, hi] at hh
    exact hh.symm
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  let zH : H := ⟨z, hzH⟩
  have hzcenter : zH ∈ center H := mem_center_iff.mpr
    (fun y => Subtype.ext (mem_center_iff.mp hzc y))
  have hcenter : (center H).map H.subtype = zpowers z := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr
      (mem_map_of_mem H.subtype hzcenter)) ?_).symm
    rw [card_map_of_injective H.subtype_injective, IsExtraspecial.center_order_p 2 H,
      Nat.card_zpowers]
    exact hz.ge
  have horder (u : S) (hzu : IsConj (z : G) (u : G)) : orderOf u = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzu
    rw [← orderOf_coe u, ← hg, ← MulAut.conj_apply]
    exact ((MulAut.conj g).orderOf_eq (z : G)).trans ((orderOf_coe z).trans hz)
  let X : Set S := {u | u ∈ H ∧ u ≠ z ∧
    ¬ ∃ v : S, v ∈ W ∧ v ≠ z ∧ IsConj (u : G) (v : G)}
  by_contra hfail
  have htX : t ∈ X := ⟨htH, hne, hfail⟩
  have hproper (u : S) (hu : u ∈ X) (hzu : IsConj (z : G) (u : G)) :
      centralizer ({u} : Set S) ≠ ⊤ := by
    intro htop
    have huC : (⟨u, hu.1⟩ : H) ∈ center H := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (show (y : S) ∈ centralizer ({u} : Set S) from
        htop ▸ mem_top _)
    have huZ : u ∈ zpowers z := hcenter ▸ mem_map_of_mem H.subtype huC
    rw [mem_zpowers_iff_mem_range_orderOf, hz] at huZ
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp huZ
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · have huone : u = 1 := by simpa using heq.symm
      have := horder u hzu
      simp [huone] at this
    · exact hu.2.1 (by simpa using heq.symm)
  have hle (u : S) (hu : u ∈ X) (hzu : IsConj (z : G) (u : G)) :
      centralizer ({u} : Set S) ≤ H := by
    by_contra hnot
    let C := centralizer ({u} : Set S)
    let C₀ := centralizer ({(⟨u, hu.1⟩ : H)} : Set H)
    have hmap : C₀.map H.subtype = H ⊓ C := map_subtype_centralizer_singleton H ⟨u, hu.1⟩
    have hlow : 16 ≤ Nat.card (H ⊓ C : Subgroup S) := by
      rw [← hmap, card_map_of_injective H.subtype_injective]
      exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two hH _
    have hrel : H.relIndex C = 2 := by
      have hd : H.relIndex C ∣ 2 := by simpa only [hi] using H.relIndex_dvd_index_of_normal C
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
      · exact (hnot (relIndex_eq_one.mp hh)).elim
      · exact hh
    have hprod := (H.subgroupOf C).card_mul_index
    have hcard : Nat.card (H.subgroupOf C) = Nat.card (H ⊓ C : Subgroup S) := by
      rw [← card_map_of_injective C.subtype_injective]
      have heq : (H.subgroupOf C).map C.subtype = H ⊓ C := by
        ext x
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨hx, x.property⟩
        · rintro ⟨hxH, hxC⟩
          exact ⟨⟨x, hxC⟩, hxH, rfl⟩
      rw [heq]
    rw [hcard, show (H.subgroupOf C).index = 2 from hrel] at hprod
    have hlC : 32 ≤ Nat.card C := by omega
    have hci := C.card_mul_index
    rw [hS] at hci
    have hindex : C.index = 2 := by
      have hcne : C.index ≠ 1 := fun hh => hproper u hu hzu (index_eq_one.mp hh)
      have hcpos : C.index ≠ 0 := by intro hh; simp [hh] at hci
      have hbound : C.index ≤ 2 := by nlinarith
      omega
    have huW := S.mem_unique_normal_four_of_centralizer_index_two hno W hunique
      z u hz hzc (horder u hzu) hu.2.1 hindex
    exact hu.2.2 ⟨u, huW, hu.2.1, IsConj.refl _⟩
  apply S.not_isConj_of_stable_centralizer_normalizers z hzc X ?_ hproper ?_ t htX hconj
  · intro u hu g hg v hgv
    refine ⟨hstable u hu.1 g hg v hgv, ?_, ?_⟩
    · intro hv
      apply hu.2.1
      apply (S : Subgroup G).subtype_injective
      apply (MulAut.conj g).injective
      have hfix : (MulAut.conj g) (z : G) = z := mul_inv_eq_iff_eq_mul.mpr hg
      exact hgv.trans ((congrArg (fun x : S => (x : G)) hv).trans hfix.symm)
    · rintro ⟨w, hwW, hwz, hvw⟩
      exact hu.2.2 ⟨w, hwW, hwz, (isConj_iff.mpr ⟨g, hgv⟩).trans hvw⟩
  · intro u hu hzu
    let C := centralizer ({u} : Set S)
    let C₀ := centralizer ({(⟨u, hu.1⟩ : H)} : Set H)
    have hmap : C₀.map H.subtype = C := by
      rw [map_subtype_centralizer_singleton, inf_eq_right.mpr (hle u hu hzu)]
    have hderived : (_root_.commutator C).map C.subtype = zpowers z := by
      rw [map_subtype_commutator, ← hmap, ← map_commutator,
        ← map_subtype_commutator,
        IsExtraspecial.centralizer_commutator_image_eq_center_of_card_thirty_two hH,
        hcenter]
    have hline : (_root_.commutator C ⊓ center C).map C.subtype = zpowers z := by
      have hc : _root_.commutator C ≤ center C := by
        intro x hx
        have hxz : (x : S) ∈ zpowers z := hderived ▸ mem_map_of_mem C.subtype hx
        have hxcenter : (x : S) ∈ center S := (zpowers_le.mpr hzc) hxz
        exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hxcenter y))
      rw [inf_eq_left.mpr hc, hderived]
    exact normalizer_map_subtype_le_centralizer_of_derived_center_line
      (S : Subgroup G) C z hz hline

end Sylow
