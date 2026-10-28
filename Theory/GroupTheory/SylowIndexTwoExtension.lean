module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# Extending a half-Sylow subgroup through an index-two section

Suppose V has index two in a Sylow two-subgroup T of G and lies in B,
where B has index two in A. Extend V to a Sylow subgroup of A. The
ambient Sylow bound and the proper index-two section force the extension
to have index exactly two over V, with intersection B equal to V.

Source application: Aschbacher–Smith C.5.6(6), printed p.157.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_mul_relIndex_of_le {V P : Subgroup G} (h : V ≤ P) :
    Nat.card V * V.relIndex P = Nat.card P := by
  simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ V P bot_le h

/-- A subgroup inside an index-two section cannot contain an ambient Sylow
subgroup. The section need not be normal in the ambient group. -/
theorem sylow_not_le_index_two_section (T : Sylow 2 G) (A B : Subgroup G)
    (hBA : B ≤ A) (hindex : B.relIndex A = 2) : ¬ (T : Subgroup G) ≤ B := by
  intro hTB
  apply T.not_dvd_index
  have hh := (relIndex_dvd_index_of_le hBA).trans (index_dvd_of_le hTB)
  rwa [hindex] at hh

/-- The required Sylow extension is constructed from Sylow's theorem;
its order and its intersection with the index-two section are forced. -/
theorem exists_sylow_index_two_extension_of_bound (A B V : Subgroup G)
    (hBA : B ≤ A) (hindex : B.relIndex A = 2)
    (hpV : IsPGroup 2 V) (hVB : V ≤ B)
    (hbound : ∀ W : Subgroup G, W ≤ A → IsPGroup 2 W → Nat.card W ≤ Nat.card V * 2) :
    ∃ P : Sylow 2 A, V ≤ (P : Subgroup A).map A.subtype ∧
      V.relIndex ((P : Subgroup A).map A.subtype) = 2 ∧
      ((P : Subgroup A).map A.subtype) ⊓ B = V := by
  have hVA := hVB.trans hBA
  obtain ⟨P, hVP⟩ := (hpV.comap_subtype (K := A)).exists_le_sylow
  let W : Subgroup G := (P : Subgroup A).map A.subtype
  have hVW : V ≤ W := by
    rw [← map_subgroupOf_eq_of_le hVA]
    exact map_mono hVP
  have hWnB : ¬ W ≤ B := by
    intro hWB
    have hPB : (P : Subgroup A) ≤ B.subgroupOf A := by
      intro p hp
      exact hWB (mem_map_of_mem A.subtype hp)
    apply P.not_dvd_index
    have hh := index_dvd_of_le hPB
    change B.relIndex A ∣ (P : Subgroup A).index at hh
    rwa [hindex] at hh
  have hcard : Nat.card W ≤ Nat.card V * 2 :=
    hbound W (map_subtype_le _) (P.isPGroup'.map A.subtype)
  have hVcard : 0 < Nat.card V := Nat.card_pos
  have hVWcard := card_mul_relIndex_of_le hVW
  have hi_ne : V.relIndex W ≠ 1 := by
    intro hi
    exact hWnB ((relIndex_eq_one.mp hi).trans hVB)
  have hi_pos : 0 < V.relIndex W := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi_lower : 2 ≤ V.relIndex W := by omega
  have hi : V.relIndex W = 2 := by nlinarith
  have hVI : V ≤ W ⊓ B := le_inf hVW hVB
  have hWI : (W ⊓ B).relIndex W ≠ 1 := by
    intro he
    exact hWnB ((relIndex_eq_one.mp he).trans inf_le_right)
  have hmul := relIndex_mul_relIndex V (W ⊓ B) W hVI inf_le_left
  rw [hi] at hmul
  have hIpos : 0 < (W ⊓ B).relIndex W := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hVIpos : 0 < V.relIndex (W ⊓ B) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hIlower : 2 ≤ (W ⊓ B).relIndex W := by omega
  have hVIone : V.relIndex (W ⊓ B) = 1 := by nlinarith
  exact ⟨P, hVW, hi, le_antisymm (relIndex_eq_one.mp hVIone) hVI⟩

/-- A two-subgroup has order at most that of an ambient Sylow subgroup. -/
theorem card_le_sylow_two {W : Subgroup G} (hp : IsPGroup 2 W) (T : Sylow 2 G) :
    Nat.card W ≤ Nat.card T := by
  obtain ⟨T', hWT'⟩ := hp.exists_le_sylow
  calc
    Nat.card W ≤ Nat.card T' := Nat.card_le_card_of_injective _ (inclusion_injective hWT')
    _ = Nat.card T := Nat.card_congr (T'.equiv T).toEquiv

/-- The ambient Sylow order supplies the bound in the extension theorem. -/
theorem exists_sylow_index_two_extension (T : Sylow 2 G) (A B V : Subgroup G)
    (hBA : B ≤ A) (hindex : B.relIndex A = 2)
    (hVT : V ≤ T) (hVB : V ≤ B) (hhalf : V.relIndex T = 2) :
    ∃ P : Sylow 2 A, V ≤ (P : Subgroup A).map A.subtype ∧
      V.relIndex ((P : Subgroup A).map A.subtype) = 2 ∧
      ((P : Subgroup A).map A.subtype) ⊓ B = V := by
  apply exists_sylow_index_two_extension_of_bound A B V hBA hindex (T.isPGroup'.to_le hVT) hVB
  intro W _ hp
  have hc := card_mul_relIndex_of_le hVT
  rw [hhalf] at hc
  exact (card_le_sylow_two hp T).trans_eq hc.symm

/-- An element in the other coset of the constructed Sylow extension
normalizes V, has square in V, and lies outside B. -/
theorem exists_normalizing_square_in_sylow_extension (T : Sylow 2 G) (A B V : Subgroup G)
    (hBA : B ≤ A) (hindex : B.relIndex A = 2)
    (hVT : V ≤ T) (hVB : V ≤ B) (hhalf : V.relIndex T = 2) :
    ∃ P : Sylow 2 A, V ≤ (P : Subgroup A).map A.subtype ∧
      V.relIndex ((P : Subgroup A).map A.subtype) = 2 ∧
      ∃ z ∈ (P : Subgroup A).map A.subtype,
        z ∉ B ∧ z ∈ normalizer (V : Set G) ∧ z ^ 2 ∈ V := by
  obtain ⟨P, hVP, hi, hinter⟩ := exists_sylow_index_two_extension T A B V hBA hindex hVT hVB hhalf
  let W : Subgroup G := (P : Subgroup A).map A.subtype
  have hn : ¬ W ≤ V := by
    intro he
    have hh := relIndex_eq_one.mpr he
    rw [hi] at hh
    omega
  obtain ⟨z, hz, hzV⟩ := SetLike.not_le_iff_exists.mp hn
  have hnorm : (V.subgroupOf W).Normal := normal_of_index_eq_two hi
  refine ⟨P, hVP, hi, z, hz, ?_,
    (normal_subgroupOf_iff_le_normalizer hVP).mp hnorm hz, ?_⟩
  · intro hzB
    exact hzV (hinter ▸ show z ∈ W ⊓ B from ⟨hz, hzB⟩)
  · exact sq_mem_of_index_two hi (⟨z, hz⟩ : W)
end Subgroup
end
