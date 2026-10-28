module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions

/-!
# Central kernels and generation in the Rudvalis branch

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the proof of
2.3.9(7), printed p.526; GLS, volume 3, Table 5.3r, printed p.279.

The quotient is the actual degree-4060 Rudvalis permutation model from
`ClassificationModels.Families`. Its nontriviality and the component's
quasisimplicity put the two-core in the center. The given inner action fixes
that kernel, so it lies in C_G(z). Consequently a subgroup whose image contains
both standard Rudvalis generators generates L together with C_G(z).

An inner representative centralizes the restricted component Sylow subgroup;
its square is central. It is not assumed to be an involution, so this reduction
also retains possible central two-covers.

The order 6048 of the simple factor in the candidate E₆₄.G₂(2) local group
is incompatible with every chi-zero quotient. This numerical obstruction does
not identify a group from its order. The 168 obstruction for the other candidate
is already available in `LieType.BlockObstructions`. Neither local subgroup
nor its factor identification is constructed here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase

open Subgroup ChapterC Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The canonical map to the concrete model, through the stated two-core quotient. -/
noncomputable def quotientMap {L : Subgroup G} {z : G}
    (d : SporadicQuotientInput L z .ru) : L →* Rudvalis.Model :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- The map retains exactly the intrinsic two-core as its kernel. -/
theorem quotientMap_ker {L : Subgroup G} {z : G}
    (d : SporadicQuotientInput L z .ru) : (quotientMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [← map_one d.quotientIso, d.quotientIso.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- Quasisimplicity and the nontrivial concrete quotient make its two-kernel central. -/
theorem twoCore_le_center {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru) :
    pCore 2 L ≤ center L := by
  let : IsQuasisimple L := h.quasisimple
  have e : (L ⧸ pCore 2 L) ≃* Rudvalis.Model := d.quotientIso
  let : Nontrivial (L ⧸ pCore 2 L) := e.symm.injective.nontrivial
  rcases IsQuasisimple.normal_le_center_or_eq_top (pCore 2 L) with hc | ht
  · exact hc
  · exact (QuotientGroup.nontrivial_iff.mp inferInstance ht).elim

/-- The actual inner action fixes the embedded two-core pointwise. -/
theorem twoCore_le_centralizer {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru) :
    L.pCoreIn 2 ≤ centralizer ({z} : Set G) := by
  obtain ⟨t, ht⟩ := d.inner
  rintro x ⟨c, hc, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hfix : d.action c = c := by
    rw [← ht]
    change t * c * t⁻¹ = c
    rw [mem_center_iff.mp (twoCore_le_center h d hc) t, mul_inv_cancel_right]
  have he := d.conjugation c
  rw [hfix] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- The embedded two-core is inside M without any assumption that it is trivial. -/
theorem twoCore_le_M {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru) :
    L.pCoreIn 2 ≤ M :=
  (twoCore_le_centralizer h d).trans h.centralizer_le

/-- An inner representative has central square and centralizes the actual component
Sylow subgroup. No involutory lift or splitting of the central kernel is asserted. -/
theorem exists_fixed_inner_lift {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru) :
    ∃ (R : Sylow 2 L) (t : L),
      (R : Subgroup L).map L.subtype = L ⊓ (S : Subgroup H).map H.subtype ∧
      MulAut.conj t = d.action ∧ t ^ 2 ∈ center L ∧ t ∉ center L ∧
      ∀ r ∈ (R : Subgroup L), Commute t r := by
  obtain ⟨R, hR, hfix⟩ := h.exists_fixed_component_sylow d.action d.conjugation
  obtain ⟨t, ht⟩ := d.inner
  refine ⟨R, t, hR, ht, ?_, ?_, ?_⟩
  · have hs : MulAut.conj (t ^ 2) = 1 := by
      rw [map_pow, ht]
      exact h.action_sq d.action d.conjugation
    apply mem_center_iff.mpr
    intro x
    have he := congrArg (fun α : MulAut L => α x) hs
    change t ^ 2 * x * (t ^ 2)⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hc
    apply h.action_ne_one d.action d.conjugation
    rw [← ht]
    apply MulEquiv.ext
    intro x
    change t * x * t⁻¹ = x
    rw [← mem_center_iff.mp hc x, mul_inv_cancel_right]
  · intro r hr
    have he := hfix r hr
    rw [← ht] at he
    change t * r * t⁻¹ = r at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- Testing the two standard generators modulo O₂(L) suffices for generation
together with C_G(z). The central kernel supplies the missing part of the lift. -/
theorem le_centralizer_sup_of_generators {H L M U : Subgroup G}
    {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru)
    (ha : Rudvalis.a ∈ (U.subgroupOf L).map (quotientMap d))
    (hb : Rudvalis.b ∈ (U.subgroupOf L).map (quotientMap d)) :
    L ≤ centralizer ({z} : Set G) ⊔ U := by
  have he := Rudvalis.eq_top_of_a_mem_of_b_mem
    ((U.subgroupOf L).map (quotientMap d)) ha hb
  have hf := congrArg (Subgroup.comap (quotientMap d)) he
  have hs : U.subgroupOf L ⊔ pCore 2 L = ⊤ := by
    simpa only [comap_map_eq, quotientMap_ker, comap_top] using hf
  have hle : U.subgroupOf L ⊔ pCore 2 L ≤
      (centralizer ({z} : Set G) ⊔ U).subgroupOf L := by
    have hu : U ≤ centralizer ({z} : Set G) ⊔ U := le_sup_right
    have hc : centralizer ({z} : Set G) ≤ centralizer ({z} : Set G) ⊔ U := le_sup_left
    refine sup_le (fun x hx => hu hx) ?_
    intro x hx
    exact hc (twoCore_le_centralizer h d ⟨x, hx, rfl⟩)
  rw [hs] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : L) ∈ ⊤ from trivial)

variable {B : Type*} [Group B]

/-- An actual quotient of order 6048 cannot be any of the chi-zero quotient models. -/
theorem not_chiZero_of_quotient_card_6048
    (hq : Nat.card (B ⧸ pCore 2 B) = 6048) : ¬ IsChiZeroBlock B := by
  intro h
  rcases LieType.chiZero_order_module h with ⟨n, _, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn5 : n < 5 := by
      by_contra hn5
      have hl : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 10 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    interval_cases n <;> norm_num [hq] at he
  · omega
  · omega

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase

end
