module

public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Best offenders from maximum elementary subgroups

Let V be a normal elementary two-subgroup contained in S. A maximum elementary
subgroup A of S has C_V(A)=V∩A. For every subgroup of A's faithful action image,
lift to B≤A and compare B C_V(B) with A. Cancelling the common action kernel
gives the best-offender inequality for the literal centralizer quotient.

This general finite-group argument is the B.2.5 input used to normalize
surviving C-components by the elementary Thompson subgroup. Source:
Aschbacher–Smith, B.2.5–7, combined manuscript of 1 March 2004, printed p.76.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
private theorem elementary_le {E A : Subgroup G} [IsElementaryAbelian 2 A]
    (h : E ≤ A) : IsElementaryAbelian 2 E := by
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact Subtype.ext (congrArg (fun a : A => (a : G))
      (mul_comm (⟨x, h x.property⟩ : A) ⟨y, h y.property⟩))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) (h x.property))

omit [Finite G] [Finite H] in
private theorem card_kernel_mul_image (q : G →* H) (A : Subgroup G) :
    Nat.card (q.ker ⊓ A : Subgroup G) * Nat.card (A.map q) = Nat.card A := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ A) A bot_le inf_le_right
  simpa only [relIndex_bot_left, inf_relIndex_right, relIndex_ker] using h

/-- The image of a maximum elementary subgroup is a best offender whenever it is nontrivial. -/
theorem maxElementary_isBestOffender
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S A : Subgroup G) (hVS : V ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S) (hne : A.map q ≠ ⊥) :
    IsBestOffender (Representation.NormalElementaryQuotient.representation V q hq hker)
      (A.map q) := by
  let ρ := Representation.NormalElementaryQuotient.representation V q hq hker
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hVA : V ⊓ centralizer (A : Set G) = V ⊓ A := by
    apply le_antisymm
    · have he : IsElementaryAbelian 2 (V ⊓ centralizer (A : Set G) : Subgroup G) :=
        elementary_le inf_le_left
      let _ := he
      have hs : IsElementaryAbelian 2 (A ⊔ (V ⊓ centralizer (A : Set G)) : Subgroup G) :=
        IsElementaryAbelian.sup_of_le_centralizer inf_le_right
      have hsup : A ⊔ (V ⊓ centralizer (A : Set G)) = A :=
        (eq_of_le_of_card_ge le_sup_left
          (hA.2.2 _ (sup_le hA.1 (inf_le_left.trans hVS)) hs)).symm
      exact le_inf inf_le_left (le_sup_right.trans_eq hsup)
    · exact inf_le_inf_left _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  refine ⟨⟨hne, inferInstance⟩, ?_⟩
  intro B hBA
  let B₀ := A ⊓ B.comap q
  have hB₀ : B₀ ≤ A := inf_le_left
  let _ : IsElementaryAbelian 2 B₀ := elementary_le hB₀
  have hmap : B₀.map q = B := by
    apply le_antisymm (map_le_iff_le_comap.mpr inf_le_right)
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBA hb
    exact mem_map_of_mem q ⟨ha, hb⟩
  have hVB : V ⊓ B₀ = V ⊓ A := by
    apply le_antisymm (inf_le_inf_left _ hB₀)
    intro v hv
    refine ⟨hv.1, hv.2, ?_⟩
    have hk : v ∈ q.ker := by
      rw [hker]
      exact (le_centralizer_iff_isMulCommutative.mpr inferInstance : V ≤ centralizer (V : Set G)) hv.1
    change q v ∈ B
    rw [show q v = 1 from hk]
    exact B.one_mem
  let C := V ⊓ centralizer (B₀ : Set G)
  let _ : IsElementaryAbelian 2 C := elementary_le inf_le_left
  have he : IsElementaryAbelian 2 (B₀ ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hmax := hA.2.2 (B₀ ⊔ C) (sup_le (hB₀.trans hA.1) (inf_le_left.trans hVS)) he
  have hBC : B₀ ⊓ C = V ⊓ A := by
    rw [← hVB]
    apply le_antisymm (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    intro v hv
    exact ⟨hv.2, hv.1,
      (le_centralizer_iff_isMulCommutative.mpr inferInstance : B₀ ≤ centralizer (B₀ : Set G)) hv.2⟩
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B₀ C
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [hBC] at hc
  have hineq : Nat.card B₀ * Nat.card C ≤ Nat.card (V ⊓ A : Subgroup G) * Nat.card A := by
    rw [hc]
    exact Nat.mul_le_mul_left _ hmax
  have hkb : q.ker ⊓ B₀ = q.ker ⊓ A := by
    apply le_antisymm (inf_le_inf_left _ hB₀)
    intro a ha
    refine ⟨ha.1, ha.2, ?_⟩
    change q a ∈ B
    rw [show q a = 1 from ha.1]
    exact B.one_mem
  have hkA := card_kernel_mul_image q A
  have hkB := card_kernel_mul_image q B₀
  rw [hkb, hmap] at hkB
  have hprod : Nat.card B * Nat.card C ≤ Nat.card (A.map q) * Nat.card (V ⊓ A : Subgroup G) := by
    have hpos : 0 < Nat.card (q.ker ⊓ A : Subgroup G) := Nat.card_pos
    nlinarith [hineq, hkA, hkB]
  have hCcard : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ B) := by
    rw [← hmap, ← Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv V q hq hker B₀)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (B₀.map q))
  have hAcard : Nat.card (V ⊓ A : Subgroup G) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.map q)) := by
    rw [← hVA, ← Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv V q hq hker A)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (A.map q))
  have hpow (D : Subgroup H) [IsElementaryAbelian 2 D] : Nat.card D = 2 ^ rank D := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_card_eq
    rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
  let _ : IsElementaryAbelian 2 B := hmap ▸ IsElementaryAbelian.map (A := B₀) q
  rw [hCcard, hAcard, hpow B, hpow (A.map q), ← pow_add, ← pow_add] at hprod
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hprod

end Representation.NormalElementaryQuotient
