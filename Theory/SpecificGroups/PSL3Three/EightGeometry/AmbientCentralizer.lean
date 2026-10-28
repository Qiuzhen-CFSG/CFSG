module
public import Theory.SpecificGroups.PSL3Three.EightGeometry.Transport
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Ambient centralizers of inner fours in the PSL₃(3) product

Under an exact identification of a complement A with Aut(PSL₃(3)), the
centralizer in A of an inner elementary four is an elementary eight.
Adjoining a disjoint central involution doubles this literal centralizer
to an elementary sixteen. The proof transports the finite-model centralizer
and decomposes the central product without changing the ambient subgroup.

Source: Aschbacher--Smith, Lemma 2.5.15, printed p.559. The application takes
the four supplied by the original largest local pair.
-/

public section
open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Three.EightGeometry
variable {G : Type*} [Group G] {H K A E : Subgroup G}

/-- The literal centralizer of an inner four in the complement is an elementary eight. -/
theorem inner_four_ambient_centralizer
    (d : A ≃* MulAut PSL) (hKA : K ≤ A)
    (hinner : K.subgroupOf A = (MulAut.innerSubgroup PSL).comap d.toMonoidHom)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hEc : Nat.card E = 4) :
    IsElementaryAbelian 2 (A ⊓ centralizer (E : Set G) : Subgroup G) ∧
      Nat.card (A ⊓ centralizer (E : Set G) : Subgroup G) = 8 := by
  let : IsElementaryAbelian 2 E := hE
  let EA := E.subgroupOf A
  have hEA : E ≤ A := hEK.trans hKA
  have hEAK : EA ≤ (MulAut.innerSubgroup PSL).comap d.toMonoidHom := by
    rw [← hinner]
    exact fun _ hx => hEK hx
  have hc : Nat.card EA = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv).trans hEc
  have hEel : IsElementaryAbelian 2 EA := IsElementaryAbelian.subgroupOf hEA
  obtain ⟨hF,hFc,_⟩ := inner_four_structure_of_equiv d EA hEAK hEel hc
  have heq : centralizer (EA : Set A) = (centralizer (E : Set G)).subgroupOf A := by
    ext a
    constructor
    · intro ha x hx
      exact congrArg Subtype.val (ha ⟨x,hEA hx⟩ hx)
    · intro ha x hx
      exact Subtype.ext (ha x hx)
  rw [heq] at hF hFc
  let hD : A ⊓ centralizer (E : Set G) ≤ A := inf_le_left
  let dF := (subgroupOfEquivOfLe hD).symm
  have hid : (A ⊓ centralizer (E : Set G)).subgroupOf A =
      (centralizer (E : Set G)).subgroupOf A := inf_subgroupOf_left (centralizer (E : Set G)) A
  let dF' := dF.trans (MulEquiv.subgroupCongr hid)
  let : IsElementaryAbelian 2 ((centralizer (E : Set G)).subgroupOf A) := hF
  exact ⟨IsElementaryAbelian.of_injective dF'.toMonoidHom dF'.injective,
    (Nat.card_congr dF'.toEquiv).trans hFc⟩

/-- Centralizing an inner four in the central involution product gives an elementary sixteen. -/
theorem inner_four_central_product_centralizer
    (d : A ≃* MulAut PSL) (hKA : K ≤ A)
    (hinner : K.subgroupOf A = (MulAut.innerSubgroup PSL).comap d.toMonoidHom)
    (t : G) (ht : orderOf t = 2) (hH : H = zpowers t ⊔ A)
    (hd : Disjoint (zpowers t) A) (hcomm : zpowers t ≤ centralizer (A : Set G))
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hEc : Nat.card E = 4) :
    H ⊓ centralizer (E : Set G) = zpowers t ⊔ (A ⊓ centralizer (E : Set G)) ∧
    IsElementaryAbelian 2 (H ⊓ centralizer (E : Set G) : Subgroup G) ∧
    Nat.card (H ⊓ centralizer (E : Set G) : Subgroup G) = 16 := by
  let C := centralizer (E : Set G)
  have hZC : zpowers t ≤ C := hcomm.trans (centralizer_le (hEK.trans hKA))
  have hsplit : H ⊓ C = zpowers t ⊔ (A ⊓ C) := by
    rw [hH]
    apply le_antisymm
    · intro x hx
      have hm : x ∈ (zpowers t : Set G) * (A : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right (zpowers t) A
          (hcomm.trans (centralizer_le_normalizer _))]
        exact hx.1
      obtain ⟨u,hu,a,ha,rfl⟩ := hm
      have haC : a ∈ C := by
        have hh := C.mul_mem (C.inv_mem (hZC hu)) hx.2
        simpa only [inv_mul_cancel_left] using hh
      exact mul_mem_sup hu ⟨ha,haC⟩
    · exact sup_le (le_inf le_sup_left hZC)
        (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  obtain ⟨hF,hFc⟩ := inner_four_ambient_centralizer d hKA hinner hEK hE hEc
  let : IsElementaryAbelian 2 (A ⊓ C : Subgroup G) := hF
  let : IsElementaryAbelian 2 (zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  have hcommF : zpowers t ≤ centralizer (A ⊓ C : Set G) :=
    hcomm.trans (centralizer_le inf_le_left)
  have hdisF : Disjoint (zpowers t) (A ⊓ C) := hd.mono_right inf_le_left
  refine ⟨hsplit, ?_, ?_⟩
  · rw [hsplit]
    exact IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hcommF)
  · rw [hsplit, card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp hcommF).trans (centralizer_le_normalizer _)) hdisF,
      Nat.card_zpowers, ht, hFc]

end Matrix.PSL3Three.EightGeometry
