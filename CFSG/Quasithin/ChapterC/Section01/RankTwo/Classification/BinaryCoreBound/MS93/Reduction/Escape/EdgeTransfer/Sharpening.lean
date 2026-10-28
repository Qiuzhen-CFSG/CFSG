module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Neighbors
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Sharpening the natural-layer bound by the actual edge action

The natural layer has order eight. When its edge displacement has order four,
nilpotent saturation puts every proper edge-invariant subgroup inside that
displacement. The neighboring kernel has a proper fixed subgroup, since its
centralizing the whole natural layer would identify the two kernels.

The neighboring displacement centralizes its own kernel. Splitting an element
of U_alpha D_alpha into the two actual factors shows that its U_alpha factor
is fixed as well: its commutator lies in both U_alpha and D_alpha, whose
intersection is trivial. This proves the requisite fixed-space lift directly
in the amalgam, without replacing relative normality by ambient normality.

The order-four premise remains explicit here. The general source owner must
prove it or establish the required neighboring sharpening by another argument.
No escape, distance-four, or edge-containment theorem is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.2)(i), printed p.882.
-/

public section

open Subgroup
open scoped commutatorElement Pointwise

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Sharpening

/-- Nilpotent saturation and the index-two displacement leave only one maximal
invariant subgroup in an eight-element group. -/
private theorem invariant_le_displacement {G : Type*} [Group G]
    (T U C : Subgroup G) [Finite T] (hT : Group.IsNilpotent T)
    (hUT : U ≤ T) (hCU : C ≤ U) (hCN : T ≤ normalizer (C : Set G))
    (hproper : ¬ U ≤ C) (hU : Nat.card U = 8)
    (hD : Nat.card (⁅U,T⁆ : Subgroup G) = 4)
    (hDU : ⁅U,T⁆ ≤ U) : C ≤ ⁅U,T⁆ := by
  let E := C ⊔ ⁅U,T⁆
  have hEU : E ≤ U := sup_le hCU hDU
  let : Finite U := Finite.of_injective (inclusion hUT) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion hEU) (inclusion_injective _)
  by_contra hnot
  have hne : ⁅U,T⁆ ≠ E := by
    intro he
    exact hnot (he ▸ (show C ≤ E from le_sup_left))
  have hlt : 4 < Nat.card E := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge le_sup_right (by omega))
  have hdvd : Nat.card E ∣ 8 := hU ▸ card_dvd_of_le hEU
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hfull : E = U := eq_of_le_of_card_ge hEU (by omega)
  exact hproper (le_of_le_sup_commutator_of_isNilpotent T U C T hT
    hUT (hCU.trans hUT) le_rfl hCN hfull.ge)

/-- Lifting fixed elements through a normalized product with disjoint factors.
This supplies the quotient-fixed transport using literal ambient products. -/
private theorem fixed_product_le {G : Type*} [Group G]
    (U D A : Subgroup G) (hUD : Disjoint U D)
    (hUN : U ≤ normalizer (D : Set G))
    (hAU : A ≤ normalizer (U : Set G)) (hAD : A ≤ normalizer (D : Set G)) :
    (U ⊔ D) ⊓ centralizer (A : Set G) ≤
      (U ⊓ centralizer (A : Set G)) ⊔ D := by
  rintro x ⟨hx, hc⟩
  have hxprod : x ∈ (U : Set G) * (D : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right U D hUN]
    exact hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hxprod
  apply mul_mem_sup
  · refine ⟨hu, ?_⟩
    intro a ha
    have hvcomm : ⁅v,a⁆ ∈ D :=
      (le_normalizer_iff_commutator_le_left.mp hAD) (commutator_mem_commutator hv ha)
    have hconj : u * ⁅v,a⁆ * u⁻¹ ∈ D := le_normalizer_iff.mp hUN u hu _ hvcomm
    have hone : (u * ⁅v,a⁆ * u⁻¹) * ⁅u,a⁆ = 1 := by
      rw [← commutatorElement_mul_left_eq_conj_mul]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc a ha).symm
    have hucD : ⁅u,a⁆ ∈ D := (D.mul_mem_cancel_left hconj).mp (hone ▸ D.one_mem)
    have hucU : ⁅u,a⁆ ∈ U :=
      (le_normalizer_iff_commutator_le_left.mp hAU) (commutator_mem_commutator hu ha)
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (show ⁅u,a⁆ = 1 from (disjoint_iff.mp hUD).le ⟨hucU, hucD⟩)).symm
  · exact hv

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Sharpening

open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Sharpening
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)

include hlarge modules in
/-- Once the edge displacement has order four, every neighboring displacement
in the natural-times-fixed layer lies in the edge-times-fixed layer. The
centralizing product lift keeps the original ambient subgroup embeddings. -/
theorem neighbor_sharpening_of_card_four (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hne : Q R a ≠ Q R d)
    (hfour : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4)
    (hnatural : ⁅Z R d, Q R b⁆ ≤ U R a ⊔ fixedCore R a) :
    ⁅Z R d, Q R b⁆ ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a := by
  let C := U R a ⊓ centralizer (Q R d : Set (FreeAmalgam R))
  have hTa : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hTd : Q R b ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdb)
  have hTU := hTa.trans (U_normalized a)
  have hA := neighbor_kernel_le_stabilizer a b d ha hab hdb
  have hUD : Disjoint (U R a) (fixedCore R a) := by
    apply disjoint_iff.mpr
    exact ((inf_le_inf_left (U R a) (show fixedCore R a ≤
      centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right)).trans
        (U_fixed_eq_bot modules a ha).le).antisymm bot_le
  have hC : C ≤ ⁅U R a, Q R b⁆ := by
    let := finite_stabilizer R b
    let : Finite (Q R b) := Finite.of_injective
      (inclusion (show Q R b ≤ stabilizer R b from fun _ hx => hx.1))
      (inclusion_injective _)
    apply invariant_le_displacement (Q R b) (U R a) C
      (edge_kernel_two source a b ha hab).isNilpotent
      ((U_le_Z a).trans (edge_Z_le_Q hlarge a b ha hab)) inf_le_left
    · exact (le_inf hTU ((hTd.trans (Q_normalized R d)).trans
        (normalizer_le_normalizer_centralizer (Q R d)))).trans
          inf_normalizer_le_normalizer_inf
    · intro h
      exact neighbor_kernel_not_centralizes modules a b d ha hab hdb hne
        (le_centralizer_iff.mp (h.trans inf_le_right))
    · exact modules.natural.card_at a ha
    · rwa [← edge_commutator_eq_natural hlarge modules a b ha hab]
    · exact le_normalizer_iff_commutator_le_left.mp hTU
  have hlift := fixed_product_le (U R a) (fixedCore R a) (Q R d) hUD
    (((U_le_Z a).trans (Z_le_stabilizer R a)).trans
      (fixedCore_normalized R a))
    (hA.trans (U_normalized a))
    (hA.trans (fixedCore_normalized R a))
  have hh := (le_inf hnatural
    (neighbor_displacement_centralizes hlarge modules a b d ha hab hdb)).trans hlift
  have hC' : C ≤ ⁅Z R a, Q R b⁆ := by
    rwa [edge_commutator_eq_natural hlarge modules a b ha hab]
  exact hh.trans (sup_le_sup_right hC' (fixedCore R a))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Sharpening
