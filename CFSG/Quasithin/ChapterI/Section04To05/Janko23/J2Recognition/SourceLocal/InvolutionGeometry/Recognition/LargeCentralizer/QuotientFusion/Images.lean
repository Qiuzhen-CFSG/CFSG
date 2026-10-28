module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Reduction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Marked images in the second centralizer quotient

The kernel of the literal map C_G(t) → C_G(t)/⟨t⟩ consists of 1 and t.
Disjointness of E and U therefore makes this map injective on E. The
image of the elementary Sylow subgroup EU has order eight; its marked
E-image has order four and index two.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}
namespace LocalFrame
variable (F : LocalFrame D t)

theorem quotient_mem_kernel_iff (ht : orderOf t = 2) (x : involutionCentralizer t) :
    x ∈ quotientKernel t ↔ x = 1 ∨ x = centralInvolution t := by
  classical
  have ho : orderOf (centralInvolution t) = 2 := by rw [← orderOf_coe]; exact ht
  rw [quotientKernel, mem_zpowers_iff_mem_range_orderOf, ho]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, pow_zero _⟩
    · exact ⟨1, by decide, pow_one _⟩

theorem quotient_eq_iff (ht : orderOf t = 2) (a b : involutionCentralizer t) :
    quotientMap t a = quotientMap t b ↔ a = b ∨ a = b * centralInvolution t := by
  change (QuotientGroup.mk a : CentralQuotient t) = QuotientGroup.mk b ↔ _
  rw [eq_comm, QuotientGroup.eq, quotient_mem_kernel_iff ht]
  constructor
  · rintro (h | h)
    · exact Or.inl (inv_mul_eq_one.mp h).symm
    · right
      have := congrArg (fun x => b * x) h
      simpa only [mul_inv_cancel_left] using this
  · rintro (rfl | rfl) <;> simp

theorem t_not_mem_E (ht : orderOf t = 2) : t ∉ F.E := by
  intro h
  exact (orderOf_eq_prime_iff.mp ht).2 (Subgroup.disjoint_def.mp F.disjoint h F.t_mem)

theorem quotient_E_injective (ht : orderOf t = 2) :
    Set.InjOn (quotientMap t) (F.E.subgroupOf (involutionCentralizer t)) := by
  intro a ha b hb hab
  rcases (quotient_eq_iff ht a b).mp hab with h | h
  · exact h
  · have hm : (b : G)⁻¹ * a ∈ F.E := F.E.mul_mem (F.E.inv_mem hb) ha
    have he : (a : G) = (b : G) * t := congrArg Subtype.val h
    rw [he, inv_mul_cancel_left] at hm
    exact (F.t_not_mem_E ht hm).elim

theorem quotient_E_card (ht : orderOf t = 2) :
    Nat.card (quotientImage F.E : Subgroup (CentralQuotient t)) = 4 := by
  let B := F.E.subgroupOf (involutionCentralizer t)
  let f : B →* CentralQuotient t := (quotientMap t).comp B.subtype
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (F.quotient_E_injective ht a.property b.property h)
  have hr : f.range = quotientImage F.E := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_map.mpr ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_left.trans F.join_le_centralizer)).toEquiv]
  exact F.E_card

theorem quotient_A_eq :
    (F.E ⊔ F.U).subgroupOf (involutionCentralizer t) = F.A := by
  rw [← F.A_eq]
  exact comap_map_eq_self_of_injective (involutionCentralizer t).subtype_injective _

def quotientSylow : Sylow 2 (CentralQuotient t) :=
  F.A.mapSurjective (QuotientGroup.mk'_surjective (quotientKernel t))

theorem quotientSylow_eq : (F.quotientSylow : Subgroup (CentralQuotient t)) =
    quotientImage (F.E ⊔ F.U) := by
  rw [quotientSylow, Sylow.coe_mapSurjective, quotientImage, F.quotient_A_eq]
  rfl

theorem quotientSylow_elementary : IsElementaryAbelian 2 F.quotientSylow := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  let : IsElementaryAbelian 2 ((F.E ⊔ F.U).subgroupOf (involutionCentralizer t)) :=
    IsElementaryAbelian.subgroupOf F.join_le_centralizer
  change IsElementaryAbelian 2 ↥(F.quotientSylow : Subgroup (CentralQuotient t))
  rw [F.quotientSylow_eq]
  exact IsElementaryAbelian.map _

theorem join_card : Nat.card (F.E ⊔ F.U : Subgroup G) = 16 := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  have hn : F.U ≤ normalizer (F.E : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro u hu
    apply mem_centralizer_iff.mpr
    intro e he
    exact congrArg Subtype.val (mul_comm (⟨e, mem_sup_left he⟩ : ↥(F.E ⊔ F.U))
      ⟨u, mem_sup_right hu⟩)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint F.E F.U hn F.disjoint,
    F.E_card, F.U_card]

theorem quotientSylow_card (ht : orderOf t = 2) : Nat.card F.quotientSylow = 8 := by
  have hk : quotientKernel t ≤ (F.A : Subgroup (involutionCentralizer t)) := by
    rw [quotientKernel, zpowers_le, ← F.quotient_A_eq]
    exact mem_sup_right F.t_mem
  have hc : Nat.card F.A = 16 := by
    rw [← card_map_of_injective (K := (F.A : Subgroup (involutionCentralizer t)))
      (involutionCentralizer t).subtype_injective, F.A_eq]
    exact F.join_card
  have h := relIndex_mul_relIndex (⊥ : Subgroup (involutionCentralizer t))
    (quotientKernel t) F.A bot_le hk
  rw [relIndex_bot_left, relIndex_bot_left, quotientKernel_card ht, hc] at h
  have hr : (quotientKernel t).relIndex F.A = Nat.card F.quotientSylow := by
    change _ = Nat.card ↥((F.A : Subgroup (involutionCentralizer t)).map (quotientMap t))
    rw [← relIndex_ker, quotientMap, QuotientGroup.ker_mk']
  rw [hr] at h
  omega

theorem quotient_E_le : quotientImage F.E ≤ (F.quotientSylow : Subgroup (CentralQuotient t)) := by
  rw [F.quotientSylow_eq]
  exact map_mono (comap_mono le_sup_left)

def quotientClosed : Subgroup F.quotientSylow :=
  (quotientImage F.E).subgroupOf (F.quotientSylow : Subgroup (CentralQuotient t))

theorem quotientClosed_eq : F.quotientClosed.map
    (F.quotientSylow : Subgroup (CentralQuotient t)).subtype = quotientImage F.E :=
  map_subgroupOf_eq_of_le F.quotient_E_le

theorem quotientClosed_index (ht : orderOf t = 2) : F.quotientClosed.index = 2 := by
  have hc : Nat.card F.quotientClosed = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe F.quotient_E_le).toEquiv).trans
      (F.quotient_E_card ht)
  have h := F.quotientClosed.index_mul_card
  rw [hc, F.quotientSylow_card ht] at h
  omega
end LocalFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
