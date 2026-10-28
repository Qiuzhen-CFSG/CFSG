module

public import Theory.GroupAction.TransitiveNonidentityCentralizer
public import Theory.GroupTheory.PGroup.TransitiveCentralInvolutionBound
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.SylowCenters
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Transitive elementary 64-subgroups in the concrete Rudvalis group

Orbit–stabilizer excludes the noncentral involution class when the actor's
order is divisible by 6048. Every point then has the actual centralizer
of order 245760, two-core of order 2048, quotient S₅ and a Sylow-center marking.

For an actor with unitary quotient whose two-core centralizes the module,
the Rudvalis two-rank places every core involution in that module. The
ambient order bounds the core by 512, so the central square-root bound
makes the entire core equal to the elementary 64-subgroup.

Source: Aschbacher–Smith 4.2.13, printed pp.611–612. The literal native
carriers and their previously checked orders and involution classes are used.
-/

public section
namespace Rudvalis
open Subgroup InvolutionCentralizers

/-- A transitive elementary 64-space with a unitary-sized actor lies in the
central involution class; its actual centralizers have their source orders. -/
theorem transitive_sixtyFour_involution_class
    (B E : Subgroup Model) [IsElementaryAbelian 2 E]
    (hBE : B ≤ normalizer (E : Set Model)) (hE : Nat.card E = 64)
    (hB : 6048 ∣ Nat.card B)
    (ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y)
    (z : E) (hz : z ≠ 1) :
    IsConj (z : Model) (b ^ 2) ∧
      Nat.card (Centralizer (z : Model)) = 245760 ∧
      Nat.card (pCore 2 (Centralizer (z : Model))) = 2048 ∧
      Nonempty ((Centralizer (z : Model) ⧸ pCore 2 (Centralizer (z : Model))) ≃*
        Equiv.Perm (Fin 5)) ∧
      ∃ P : Sylow 2 Model, (center P).map (P : Subgroup Model).subtype = zpowers (z : Model) := by
  have ho : orderOf (z : Model) = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian _ z.property,fun h => hz (Subtype.ext h)⟩
  have hh := Theory.GroupAction.centralizer_card_mul_pred_of_transitive B E hBE ht z hz
  rw [hE] at hh
  have hd : 96 ∣ Nat.card ((centralizer ({(z : Model)} : Set Model)).subgroupOf B) := by
    have hmul : 96 * 63 ∣
        Nat.card ((centralizer ({(z : Model)} : Set Model)).subgroupOf B) * 63 := by
      rw [hh]
      exact hB
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 63)).mp hmul
  have hc : 96 ∣ Nat.card (Centralizer (z : Model)) := by
    let j : (centralizer ({(z : Model)} : Set Model)).subgroupOf B →*
        Centralizer (z : Model) :=
      { toFun := fun x => ⟨x.val.val,x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    exact hd.trans (card_dvd_of_injective j (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun w : Centralizer (z : Model) => (w : Model)) h))))
  have hclass : IsConj (z : Model) (b ^ 2) := by
    rcases centralizer_representatives (z : Model) ho with h | h
    · exact h.1
    · rw [second_class_centralizer_card h.1] at hc
      norm_num at hc
  exact ⟨hclass,first_centralizer_card hclass,first_core_card hclass,
    ⟨firstQuotientEquiv hclass⟩,exists_sylow_center_eq_of_isConj_square _ ho hclass⟩
end Rudvalis

namespace Rudvalis
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

/-- The literal unitary actor has exactly its transitive E64 as two-core.
The proof uses the checked Rudvalis two-part and rank, not a local catalogue. -/
theorem transitive_sixtyFour_twoCore
    (B E : Subgroup Model) [IsElementaryAbelian 2 E]
    (hEB : E ≤ B) (hBE : B ≤ normalizer (E : Set Model))
    (hE : Nat.card E = 64)
    (a : B ⧸ pCore 2 B ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set Model))
    (ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y) :
    B.pCoreIn 2 = E ∧ Nat.card B = 64 * 6048 := by
  have hEP : E ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 E) hEB hBE
  let P := pCore 2 B
  let F := (E.subgroupOf B).subgroupOf P
  have hEP' : E.subgroupOf B ≤ P := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hEP hx
    exact B.subtype_injective he ▸ hy
  let eF : F ≃* E := (subgroupOfEquivOfLe hEP').trans (subgroupOfEquivOfLe hEB)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_surjective eF.symm.toMonoidHom eF.symm.surjective
  have hF : Nat.card F = 64 := (Nat.card_congr eF.toEquiv).trans hE
  have hcent : F ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subtype.ext (hcore (mem_map_of_mem B.subtype y.property) x hx).symm)
  have hInv : ∀ x : P, x^2 = 1 → x ∈ F := by
    intro x hx
    let C := E ⊔ zpowers (x : Model)
    let : IsElementaryAbelian 2 (zpowers (x : Model)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (congrArg (fun z : P => (z : Model)) hx)
    have hcomm : zpowers (x : Model) ≤ centralizer (E : Set Model) :=
      zpowers_le.mpr (hcore (mem_map_of_mem B.subtype x.property))
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.sup_of_le_centralizer
      hcomm
    have hC : Nat.card C ≤ 64 := (primeRank_le_iff_elementary_card_le Model).mp
      primeRank_le_six C inferInstance
    have he : C = E := (eq_of_le_of_card_ge (show E ≤ C from le_sup_left)
      (by rw [hE]; exact hC)).symm
    have hxC : (x : Model) ∈ C := mem_sup_right (mem_zpowers _)
    change (x : Model) ∈ E
    exact he ▸ hxC
  have htrans : ∀ x ∈ F, ∀ y ∈ F, x ≠ 1 → y ≠ 1 → ∃ α : MulAut P, α x = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨b,hb,he⟩ := ht x hx y hy
      (fun h => hx1 (Subtype.ext (Subtype.ext h)))
      (fun h => hy1 (Subtype.ext (Subtype.ext h)))
    exact ⟨MulAut.conjNormal (⟨b,hb⟩ : B),Subtype.ext (Subtype.ext he)⟩
  have hquot : Nat.card (B ⧸ P) = 6048 := by
    rw [Nat.card_congr a.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  have hprod : Nat.card P * 6048 = Nat.card B := by
    have h := P.card_mul_index
    rw [index_eq_card,hquot] at h
    exact h
  have hsmall : Nat.card P ≤ 512 := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    have hd : Nat.card P * 6048 ∣ 512 * 47125 * 6048 := by
      rw [hprod]
      have h := B.card_subgroup_dvd_card
      rw [model_card] at h
      exact h
    have hd' := (Nat.mul_dvd_mul_iff_right (by decide : 0 < 6048)).mp hd
    rw [hn] at hd'
    have hdiv : 2 ^ n ∣ 512 :=
      ((by decide : Nat.Coprime 2 47125).pow_left n).dvd_of_dvd_mul_right hd'
    rw [hn]
    exact Nat.le_of_dvd (by decide) hdiv
  have htop := eq_top_of_transitive_central_involutions (pCore_isPGroup (p := 2) (G := B))
    F hcent hInv htrans (by
      change Nat.card P < Nat.card F * Nat.card F
      rw [hF]
      omega)
  have hPE : B.pCoreIn 2 = E := by
    apply le_antisymm _ hEP
    rintro x ⟨y,hy,rfl⟩
    exact (show (⟨y,hy⟩ : P) ∈ F from htop.symm ▸ mem_top _)
  refine ⟨hPE,?_⟩
  have hp : Nat.card P = 64 := by
    have h := congrArg (fun X : Subgroup Model => Nat.card X) hPE
    change Nat.card (P.map B.subtype) = Nat.card E at h
    rw [card_map_of_injective B.subtype_injective,hE] at h
    exact h
  rw [hp] at hprod
  exact hprod.symm
end Rudvalis
