module
public import Stellmacher.Recognition.Parrott.DerivedTCentralizerCore
public import Theory.GroupAction.InvariantHyperplaneDisplacement
public import Theory.GroupAction.FiveFourSquareFixed
public import Stellmacher.Recognition.Parrott.DerivedVHyperplane
public import Theory.GroupTheory.CyclicExtensionDerivedBound
/-!
# The derived image of the first centralizer modulo the derived core

The image of C_J(t) in J/J′ is an invariant hyperplane for an order-four
actor in C_T(t). That hyperplane is the actor's displacement image, so
its own displacements are fixed by the square. The cyclic-extension
calculation therefore puts the actual image of C_T(t)′ in this square
fixed subgroup, the subgroup denoted B/E by Parrott.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the last two paragraphs of p.676.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
/-- The derived image of the order-1024 centralizer is fixed by the square of a quotient generator. -/
public theorem t_centralizer_derived_quotient_square_fixed
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    let q := QuotientGroup.mk' (commutator J)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 →
      ∀ f : (H ⧸ J) →* MulAut (J ⧸ commutator J), Function.Injective f →
        (∀ (a : H) (b b' : J), (b' : H) = a * (b : H) * a⁻¹ →
          f (QuotientGroup.mk' J a) (q b) = q b') →
      ∃ y : H, (y : G) ∈ C ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧
        ∀ b : J, i b ∈ (commutator C).map C.subtype →
          f (QuotientGroup.mk' J y) (f (QuotientGroup.mk' J y) (q b)) = q b := by
  intro H J i E q t ht htz C hC f hf heval
  let CH := C.subgroupOf H
  have hCH : C ≤ H := inf_le_left.trans (by rw [d.sylow_map]; exact map_subtype_le _)
  let U := ((centralizer ({t} : Set G)).comap i).map q
  obtain ⟨hElem, hWcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 (J ⧸ commutator J) := hElem
  obtain ⟨y, hy, hyorder⟩ := d.t_centralizer_exists_quotient_order_four h t ht htz hC
  let a := f (QuotientGroup.mk' J y)
  have ha4 : a ^ 4 = 1 := by
    have ho := (orderOf_injective f hf (QuotientGroup.mk' J y)).trans hyorder
    exact ho ▸ pow_orderOf_eq_one a
  have hCHcore : CH.comap J.subtype = (centralizer ({t} : Set G)).comap i := by
    ext b
    change i b ∈ C ↔ i b ∈ centralizer ({t} : Set G)
    exact and_iff_right (d.core_le_sylow (mem_map_of_mem H.subtype b.property))
  have hUcard : Nat.card U = 8 :=
    (parrott_derived_core_centralizer_hyperplane z h t ht htz).2.2
  have hUindex : U.index = 2 := by
    have hh := U.card_mul_index
    rw [hUcard, hWcard] at hh
    omega
  have hstable : ∀ u ∈ U, a u ∈ U := by
    rintro u ⟨b, hb, rfl⟩
    let b' : J := ⟨y * (b : H) * y⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : J.Normal) b b.property y⟩
    rw [show a (q b) = q b' from heval y b b' rfl]
    apply mem_map_of_mem
    exact (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).mul_mem hy.2 hb)
      ((centralizer ({t} : Set G)).inv_mem hy.2)
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  have hfixed : Nat.card (FixedPoints.subgroup (zpowers a) (J ⧸ commutator J)) = 2 := by
    have hh := (Theory.GroupAction.five_four_sixteen_order_four_fixed_cards hWcard φ hφ
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)
      (e (QuotientGroup.mk' J y)) ((e.orderOf_eq _).trans hyorder)).1
    change Nat.card (FixedPoints.subgroup
      (zpowers (f (e.symm (e (QuotientGroup.mk' J y))))) (J ⧸ commutator J)) = 2 at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  have hmapcard : Nat.card (CH.map (QuotientGroup.mk' J)) = 4 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    have hh := d.t_centralizer_core_relIndex h t ht htz hC
    have heq : J.relIndex CH = (J.map H.subtype).relIndex C := by
      rw [← relIndex_map_map_of_injective J CH H.subtype_injective,
        map_subgroupOf_eq_of_le hCH]
    rwa [heq]
  have hmap : CH.map (QuotientGroup.mk' J) = zpowers (QuotientGroup.mk' J y) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem (QuotientGroup.mk' J) (show y ∈ CH from hy)))
    rw [Nat.card_zpowers, hyorder, hmapcard]
  let R := FixedPoints.subgroup (zpowers (a ^ 2)) (J ⧸ commutator J)
  have hbound := Theory.GroupTheory.cyclic_extension_derived_le_of_displacement_le
    J CH f heval y hy hmap R
    (by simpa only [hCHcore] using hstable)
    (by
      rw [hCHcore]
      intro u hu
      apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
      exact MulAut.displacement_square_fixed_of_invariant_index_two
        a ha4 hfixed U hUindex hstable u hu)
  refine ⟨y, hy, hyorder, ?_⟩
  intro b hb
  suffices hh : q b ∈ R by
    simpa only [pow_two, MulAut.mul_apply] using
      (MulAut.mem_fixed_zpowers_iff (a ^ 2) (q b)).mp hh
  apply hbound
  apply mem_map_of_mem
  change (b : H) ∈ (commutator CH).map CH.subtype
  have hmapD : ((commutator CH).map CH.subtype).map H.subtype =
      (commutator C).map C.subtype := by
    rw [map_subtype_commutator, map_commutator, map_subgroupOf_eq_of_le hCH,
      map_subtype_commutator]
  have hm : (b : H).val ∈ ((commutator CH).map CH.subtype).map H.subtype := hmapD ▸ hb
  obtain ⟨c, hc, hcb⟩ := hm
  exact H.subtype_injective hcb ▸ hc
end Stellmacher.Recognition.ParrottSecondElementaryData
