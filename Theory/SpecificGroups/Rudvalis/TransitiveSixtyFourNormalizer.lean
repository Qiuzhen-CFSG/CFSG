module

public import Theory.SpecificGroups.Rudvalis.TransitiveSixtyFour
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreRestriction

/-!
# Two-cores above a transitive Rudvalis unitary actor

Let B have order 64·6048 and two-core E, an elementary group of order 64
on whose nonidentity elements B acts transitively. Every overgroup of B
normalizing E has the same two-core. Irreducibility centralizes this core
on E. The Rudvalis two-rank puts all core involutions in E; the product
order with B bounds the core by 512. Transitivity and the central
square-root-fiber bound then identify the entire core with E.

This is applied to the literal source normalizer in
OriginalOddNormalizer.RudvalisNormalizer. No maximality, Sylow containment,
or normalizer order is assumed.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
namespace Rudvalis
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

/-- A normalizing overgroup has exactly the original elementary 64-subgroup
as its two-core. -/
theorem transitive_sixtyFour_overgroup_core
    (B E N : Subgroup Model) [IsElementaryAbelian 2 E]
    (hEB : E ≤ B) (hBN : B ≤ N) (hNE : N ≤ normalizer (E : Set Model))
    (hE : Nat.card E = 64) (hB : Nat.card B = 64 * 6048)
    (hBE : B.pCoreIn 2 = E)
    (ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y) :
    N.pCoreIn 2 = E := by
  have hEN := hEB.trans hBN
  have hEP : E ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 E) hEN hNE
  have hirr : ∀ U : Subgroup Model, U ≤ E → B ≤ normalizer (U : Set Model) →
      U = ⊥ ∨ U = E := by
    intro U hU hBU
    by_cases hu : U = ⊥
    · exact Or.inl hu
    apply Or.inr
    obtain ⟨x,hx1⟩ := (ne_bot_iff_exists_ne_one).mp hu
    apply le_antisymm hU
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ U.one_mem
    obtain ⟨b,hb,he⟩ := ht x (hU x.property) y hy (fun he => hx1 (Subtype.ext he)) hy1
    exact he ▸ (mem_normalizer_iff.mp (hBU hb) x).mp x.property
  have hPC := pCoreIn_le_centralizer_of_irreducible E B N
    (IsElementaryAbelian.isPGroup 2 E) hEN hNE hBN hirr
  let P := pCore 2 N
  let F := (E.subgroupOf N).subgroupOf P
  have hEP' : E.subgroupOf N ≤ P := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hEP hx
    exact N.subtype_injective he ▸ hy
  let eF : F ≃* E := (subgroupOfEquivOfLe hEP').trans (subgroupOfEquivOfLe hEN)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_surjective eF.symm.toMonoidHom eF.symm.surjective
  have hF : Nat.card F = 64 := (Nat.card_congr eF.toEquiv).trans hE
  have hcent : F ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subtype.ext (hPC (mem_map_of_mem N.subtype y.property) x hx).symm)
  have hInv : ∀ x : P, x^2 = 1 → x ∈ F := by
    intro x hx
    let C := E ⊔ zpowers (x : Model)
    let : IsElementaryAbelian 2 (zpowers (x : Model)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (congrArg (fun z : P => (z : Model)) hx)
    have hcomm : zpowers (x : Model) ≤ centralizer (E : Set Model) :=
      zpowers_le.mpr (hPC (mem_map_of_mem N.subtype x.property))
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.sup_of_le_centralizer hcomm
    have hC : Nat.card C ≤ 64 := (primeRank_le_iff_elementary_card_le Model).mp
      primeRank_le_six C inferInstance
    have he : C = E := (eq_of_le_of_card_ge (show E ≤ C from le_sup_left)
      (by rw [hE]; exact hC)).symm
    change (x : Model) ∈ E
    exact he ▸ (show (x : Model) ∈ C from mem_sup_right (mem_zpowers _))
  have htrans : ∀ x ∈ F, ∀ y ∈ F, x ≠ 1 → y ≠ 1 → ∃ α : MulAut P, α x = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨b,hb,he⟩ := ht x hx y hy
      (fun h => hx1 (Subtype.ext (Subtype.ext h)))
      (fun h => hy1 (Subtype.ext (Subtype.ext h)))
    exact ⟨MulAut.conjNormal (⟨b,hBN hb⟩ : N),Subtype.ext (Subtype.ext he)⟩
  have hi : N.pCoreIn 2 ⊓ B = E := by
    apply le_antisymm
    · rw [inf_comm]
      exact (inf_pCoreIn_le_of_le 2 hBN).trans hBE.le
    · exact le_inf hEP hEB
  have hsmall : Nat.card P ≤ 512 := by
    have hn : B ≤ normalizer (N.pCoreIn 2 : Set Model) :=
      hBN.trans (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N P))
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (N.pCoreIn 2) B hn
    rw [hi,hE,hB] at hh
    change Nat.card (P.map N.subtype) * (64 * 6048) =
      64 * Nat.card (N.pCoreIn 2 ⊔ B : Subgroup Model) at hh
    rw [card_map_of_injective N.subtype_injective] at hh
    have hprod : Nat.card P * 6048 = Nat.card (N.pCoreIn 2 ⊔ B : Subgroup Model) := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 64)
      simpa only [←Nat.mul_assoc, Nat.mul_comm 64 (Nat.card P)] using hh
    obtain ⟨n,hp⟩ := (pCore_isPGroup (p := 2) (G := N)).exists_card_eq
    have hd : Nat.card P * 6048 ∣ 512 * 47125 * 6048 := by
      rw [hprod]
      have hh := (N.pCoreIn 2 ⊔ B).card_subgroup_dvd_card
      rw [model_card] at hh
      exact hh
    have hd' := (Nat.mul_dvd_mul_iff_right (by decide : 0 < 6048)).mp hd
    rw [hp] at hd'
    have hdiv : 2 ^ n ∣ 512 :=
      ((by decide : Nat.Coprime 2 47125).pow_left n).dvd_of_dvd_mul_right hd'
    rw [hp]
    exact Nat.le_of_dvd (by decide) hdiv
  have htop := eq_top_of_transitive_central_involutions (pCore_isPGroup (p := 2) (G := N))
    F hcent hInv htrans (by
      change Nat.card P < Nat.card F * Nat.card F
      rw [hF]
      omega)
  apply le_antisymm _ hEP
  rintro x ⟨y,hy,rfl⟩
  exact (show (⟨y,hy⟩ : P) ∈ F from htop.symm ▸ mem_top _)

end Rudvalis
