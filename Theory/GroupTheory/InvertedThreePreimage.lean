module

public import Theory.GroupTheory.InvertedThreeLift
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Mathlib.GroupTheory.Sylow

/-!
# An involution-normalized Sylow three preimage

An order-two subgroup with nontrivial image in S₃ normalizes a three-subgroup
whose join with it is S₃. Under a surjection from a group with Sylow
three-subgroups of order three, this subgroup is the image of an actual Sylow
subgroup. The original order-two image normalizes its full preimage.

The proof extracts an inverted element from two conjugate involutions, then
uses Sylow lifting; no splitting or amalgam recognition is assumed.
This is the quotient argument in Aschbacher–Smith J.4.4(5), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- A prescribed order-two subgroup over S₃ lies in an actual S₃ subgroup. -/
theorem exists_normalized_three_join_of_perm_three
    (f : D →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (B : Subgroup D) (hB : Nat.card B = 2) (himage : B.map f ≠ ⊥) :
    ∃ Y : Subgroup D, Nat.card Y = 3 ∧ B ≤ normalizer (Y : Set D) ∧
      Nonempty ((B ⊔ Y : Subgroup D) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 (by rw [hB])
  have hwD : orderOf (w : D) = 2 := (orderOf_coe w).trans hw
  have hwgen : zpowers (w : D) = B := eq_of_le_of_card_ge
    (zpowers_le.mpr w.property) (by rw [Nat.card_zpowers,hwD,hB])
  have hfw : f w ≠ 1 := by
    intro h
    apply himage
    rw [← hwgen,MonoidHom.map_zpowers,h,zpowers_one_eq_bot]
  obtain ⟨Y,hY,hwY,hinv⟩ := exists_inverted_three_of_surjective_perm_three f hf (w:D)
    (by simpa only [hwD] using pow_orderOf_eq_one (w:D)) hfw
  have hBY : B ≤ normalizer (Y : Set D) := by
    rw [← hwgen]
    exact zpowers_le.mpr hwY
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 (by rw [hY])
  have hyD : orderOf (y:D) = 3 := (orderOf_coe y).trans hy
  have hygen : zpowers (y:D) = Y := eq_of_le_of_card_ge
    (zpowers_le.mpr y.property) (by rw [Nat.card_zpowers,hyD,hY])
  have hout : (w:D) ∉ zpowers (y:D) := by
    intro hm
    have hd := _root_.orderOf_dvd_natCard (⟨(w:D),hygen ▸ hm⟩ : Y)
    rw [← orderOf_coe,hwD,hY] at hd
    norm_num at hd
  obtain ⟨_,⟨e⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion (by decide : 0 < 3)
    (y:D) (w:D) hyD (by simpa only [hwD] using pow_orderOf_eq_one (w:D)) hout
    (hinv y y.property)
  obtain ⟨e3⟩ := Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
  refine ⟨Y,hY,hBY,?_⟩
  rw [← hwgen,← hygen,sup_comm]
  exact ⟨e.trans e3⟩

/-- The preceding three-subgroup lifts to a Sylow subgroup without changing
its normalizing image. The join is identified through the literal map. -/
theorem exists_sylow_three_normalized_preimage
    (q : G →* D) (hq : Function.Surjective q)
    (hthree : ∀ X : Sylow 3 G, Nat.card X = 3)
    (f : D →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (B : Subgroup G) (hB : Nat.card (B.map q) = 2)
    (himage : (B.map q).map f ≠ ⊥) :
    ∃ X : Sylow 3 G,
      B ≤ normalizer (((X : Subgroup G) ⊔ q.ker : Subgroup G) : Set G) ∧
      Nonempty ((((B ⊔ (X : Subgroup G)) ⊔ q.ker).map q) ≃* Equiv.Perm (Fin 3)) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Y,hY,hBY,⟨e⟩⟩ := exists_normalized_three_join_of_perm_three f hf (B.map q) hB himage
  obtain ⟨P,hYP⟩ := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hY)).exists_le_sylow
  obtain ⟨X,hX⟩ := Sylow.mapSurjective_surjective hq 3 P
  have hXP : (X : Subgroup G).map q = (P : Subgroup D) := congrArg Sylow.toSubgroup hX
  have hXY : (X : Subgroup G).map q = Y := by
    rw [hXP]
    apply (eq_of_le_of_card_ge hYP ?_).symm
    calc Nat.card Y = 3 := hY
         _ = Nat.card X := (hthree X).symm
         _ ≥ Nat.card (P : Subgroup D) := by
           rw [← hXP]
           exact Nat.card_le_card_of_surjective (q.subgroupMap (X : Subgroup G))
             (q.subgroupMap_surjective _)
  have hpre : Y.comap q = (X : Subgroup G) ⊔ q.ker := by
    rw [← hXY,comap_map_eq]
  refine ⟨X,?_,?_⟩
  · rw [← hpre]
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    change q x ∈ Y ↔ q (b*x*b⁻¹) ∈ Y
    simpa only [map_mul,map_inv] using mem_normalizer_iff.mp (hBY (mem_map_of_mem q hb)) (q x)
  · rw [map_sup,map_sup,hXY,map_ker_self,sup_bot_eq]
    exact ⟨e⟩
end Subgroup
