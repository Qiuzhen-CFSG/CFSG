module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.OuterActions
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence
/-!
# The complete prime component-product conclusions

The actual right two-core is a four-group inside the selected component.
It normalizes the original left cubic residual, so its transported images
in the prime PSL₂ model force the source congruence modulo twenty-four.
The concluding theorem joins this calculation to the literal product,
local dihedral and symmetric models, and both outer actions.

Source: Aschbacher–Smith F.6.17(2) and F.6.18(3), printed pp.309–310.
The component model and cubic input are supplied by the earlier source
component sieve and F.6.13 reduction, respectively.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable {G₁ G₂ : Subgroup G} {p : ℕ} [Fact p.Prime]
theorem SingleResidualComponent.source_prime_congruence
    (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  let K := d.component
  let Q := (pCore 2 G₂).map G₂.subtype
  let A := (pResidual 2 G₁).map G₁.subtype
  obtain ⟨_,_,⟨j⟩⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  obtain ⟨hQK,hQc,_,_,_,_⟩ := d.source_prime_local_models e h hp hm hc
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp (twoCore_le_primeToThreeCore.trans_eq
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e))
  obtain ⟨hQ,_,_⟩ := right_core_small_elementary_of_not_characteristic_two h hcore
    (left_not_characteristic_two_of_cubic h hc)
  let : IsElementaryAbelian 2 Q := hQ
  let : IsElementaryAbelian 2 (Q.subgroupOf K) := IsElementaryAbelian.subgroupOf hQK
  let V := (Q.subgroupOf K).map j.toMonoidHom
  let B := (A.subgroupOf K).map j.toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map j.toMonoidHom
  have hV : Nat.card V = 4 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv]
    exact hQc
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; decide)
  let : IsKleinFour V := ⟨hV,IsElementaryAbelian.exponent_eq_prime⟩
  have hB : Nat.card B = 3 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe d.left_contains).toEquiv]
    exact hc
  have hQT : Q ≤ G₁ ⊓ G₂ := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
  have hnK : Q.subgroupOf K ≤ normalizer (A.subgroupOf K : Set K) := by
    apply le_normalizer_iff.mpr
    intro s hs a ha
    change (s : G) * (a : G) * (s : G)⁻¹ ∈ A
    exact (mem_normalizer_iff.mp (h.intersection_normalizes_left_residual (hQT hs)) (a : G)).mp ha
  have hn : V ≤ normalizer (B : Set PSL(2,ZMod p)) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hnK
  exact Theory.PSL2.prime_mod24_of_four_normalizes_cubic hp h8 V B hB hn


/-- All row-three conclusions, retaining the source factors and multiplication. -/
theorem SingleResidualComponent.source_prime_conclusion
    (d : SingleResidualComponent G₁ G₂)
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hm : ClassicalGroup.IsPSL (d.component ⧸ center d.component) 2 p)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    let D := pResidual 2 G ⊓ centralizer (d.component : Set G)
    (p % 24 = 11 ∨ p % 24 = 13) ∧
      Nonempty (G₁ ≃* DihedralGroup 12) ∧
      Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) ∧
      D.Normal ∧ Nat.card D = 3 ∧ d.component ⊔ D = pResidual 2 G ∧
      Disjoint d.component D ∧ Nonempty (d.component ≃* PSL(2,ZMod p)) ∧
      (∃ f : d.component × D ≃* pResidual 2 G,
        ∀ k a, (f (k,a) : G) = (k : G) * (a : G)) ∧
      (∀ t : G, t ∈ G₁ ⊓ G₂ → t ∉ d.component →
        (∃ α : MulAut d.component,
          (∀ a : d.component, (α a : G) = t * (a : G) * t⁻¹) ∧
          α ∉ MulAut.innerSubgroup d.component) ∧
        (∃ β : MulAut D, (∀ a : D, (β a : G) = t * (a : G) * t⁻¹) ∧
          β ∉ MulAut.innerSubgroup D)) ∧
      ∃ t : G, t ∈ G₁ ⊓ G₂ ∧ t ∉ d.component ∧
        (∃ α : MulAut d.component,
          (∀ a : d.component, (α a : G) = t * (a : G) * t⁻¹) ∧
          α ∉ MulAut.innerSubgroup d.component) ∧
        (∃ β : MulAut D, (∀ a : D, (β a : G) = t * (a : G) * t⁻¹) ∧
          β ∉ MulAut.innerSubgroup D) := by
  obtain ⟨_,_,_,_,hr,ht⟩ := d.source_prime_local_models e h hp hm hc
  obtain ⟨hD,hDc,hs,hd,hprod⟩ := d.prime_product e h hp hm
  obtain ⟨_,_,hj⟩ := prime_psl_component_center_and_outer e d.isComponent hp hm
  exact ⟨d.source_prime_congruence e h hp h8 hm hc,
    d.source_prime_left_dihedral e h hp hm hc,hr,ht,hD,hDc,hs,hd,hj,hprod,
    d.source_prime_outer_actions_all e h hp hm hc,
    d.source_prime_outer_actions e h hp hm hc⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
