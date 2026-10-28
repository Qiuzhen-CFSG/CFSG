module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Symmetric commutator planes of conjugate elementary subgroups

Suppose every moving involution on V has equal displacement and fixed
planes, each containing a distinguished line Z. Mutual normalization of
V and its conjugate traps their commutator between those two planes.
Transitivity outside Z then permits adjusting the conjugator by an element
normalizing V so that it fixes the literal commutator plane. The proof uses
the inverse conjugate to obtain the second plane and makes the adjustment
explicit with the left-conjugation convention.

This is the symmetric-plane step in Aschbacher–Smith, B.4.8(2) and 12.4.9,
printed pp.91 and 816. No fusion assumption is used.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem plane_eq_sup (Z P : Subgroup G) (hZ : Nat.card Z = 2)
    (hP : Nat.card P = 4) (hZP : Z ≤ P) (x : G) (hx : x ∈ P) (hxZ : x ∉ Z) :
    P = Z ⊔ zpowers x := by
  have hs : Z ⊔ zpowers x ≤ P := sup_le hZP (zpowers_le_of_mem hx)
  have hd : 2 ∣ Nat.card (Z ⊔ zpowers x : Subgroup G) :=
    hZ ▸ card_dvd_of_le (show Z ≤ Z ⊔ zpowers x from le_sup_left)
  have hlo : 2 < Nat.card (Z ⊔ zpowers x : Subgroup G) := by
    by_contra hn
    have he : Z = Z ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (by omega)
    exact hxZ (he ▸ (le_sup_right : zpowers x ≤ Z ⊔ zpowers x) (mem_zpowers x))
  have hhi := card_le_of_le hs
  apply (eq_of_le_of_card_ge hs ?_).symm
  omega

/-- Transitivity off a fixed line gives transitivity on planes containing it. -/
theorem conjugate_planes_of_transitive_nonfixed
    (V Z L : Subgroup G) (hZ : Nat.card Z = 2)
    (hLZ : L ≤ centralizer (Z : Set G))
    (horbit : ∀ x ∈ V, x ∉ Z → ∀ y ∈ V, y ∉ Z →
      ∃ l ∈ L, MulAut.conj l x = y)
    (P Q : Subgroup G) (hPV : P ≤ V) (hQV : Q ≤ V)
    (hZP : Z ≤ P) (hZQ : Z ≤ Q) (hP : Nat.card P = 4) (hQ : Nat.card Q = 4) :
    ∃ l ∈ L, P.map (MulAut.conj l).toMonoidHom = Q := by
  have hnot (R : Subgroup G) (hR : Nat.card R = 4) : ¬ R ≤ Z := by
    intro hle
    have := card_le_of_le hle
    omega
  obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp (hnot P hP)
  obtain ⟨y, hy, hyZ⟩ := Set.not_subset.mp (hnot Q hQ)
  obtain ⟨l, hl, he⟩ := horbit x (hPV hx) hxZ y (hQV hy) hyZ
  refine ⟨l, hl, ?_⟩
  rw [plane_eq_sup Z P hZ hP hZP x hx hxZ,
    plane_eq_sup Z Q hZ hQ hZQ y hy hyZ, map_sup]
  have hfix : Z.map (MulAut.conj l).toMonoidHom = Z := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change l * z * l⁻¹ ∈ Z
      rwa [(hLZ hl z hz).symm, mul_inv_cancel_right]
    · intro z hz
      refine ⟨z, hz, ?_⟩
      change l * z * l⁻¹ = z
      rw [(hLZ hl z hz).symm, mul_inv_cancel_right]
  rw [hfix, MonoidHom.map_zpowers]
  change Z ⊔ zpowers (MulAut.conj l x) = Z ⊔ zpowers y
  rw [he]

omit [Finite G] in
/-- Mutual normalization traps the commutator between an involution's
displacement plane and the same involution's fixed plane. -/
theorem commutator_plane_of_involution_planes
    (V Z A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAV : A ≤ normalizer (V : Set G)) (hVA : V ≤ normalizer (A : Set G))
    (hmove : ⁅V, A⁆ ≠ ⊥)
    (hplanes : ∀ a ∈ normalizer (V : Set G), a ^ 2 = 1 →
      a ∉ centralizer (V : Set G) →
      Z ≤ ⁅V, zpowers a⁆ ∧ ⁅V, zpowers a⁆ = V ⊓ centralizer ({a} : Set G) ∧
        Nat.card (⁅V, zpowers a⁆ : Subgroup G) = 4) :
    Z ≤ ⁅V, A⁆ ∧ Nat.card (⁅V, A⁆ : Subgroup G) = 4 := by
  have hn : ¬ A ≤ centralizer (V : Set G) := by
    intro hc
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hn
  obtain ⟨hZ, he, hc⟩ := hplanes a (hAV ha)
    (elemPow_eq_one_of_isElementaryAbelian a ha) hna
  have hsmall : ⁅V, zpowers a⁆ ≤ ⁅V, A⁆ :=
    commutator_mono le_rfl (zpowers_le_of_mem ha)
  have hDV : ⁅V, A⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hAV
  have hDA : ⁅V, A⁆ ≤ A := le_normalizer_iff_commutator_le_right.mp hVA
  have hbig : ⁅V, A⁆ ≤ ⁅V, zpowers a⁆ := by
    rw [he]
    refine le_inf hDV ?_
    intro d hd
    apply mem_centralizer_singleton_iff.mpr
    exact ((le_centralizer A (hDA hd)) a ha).symm
  have heq := le_antisymm hsmall hbig
  exact ⟨heq ▸ hZ, heq ▸ hc⟩

/-- Adjust a conjugator inside the normalizer of V so that the literal
commutator plane is invariant. The inverse conjugate supplies the second
plane; no fusion assertion is used. -/
theorem exists_symmetric_commutator_plane
    (V Z L : Subgroup G) [IsElementaryAbelian 2 V]
    (hZ : Nat.card Z = 2) (hL : L ≤ normalizer (V : Set G))
    (hLZ : L ≤ centralizer (Z : Set G))
    (horbit : ∀ x ∈ V, x ∉ Z → ∀ y ∈ V, y ∉ Z →
      ∃ l ∈ L, MulAut.conj l x = y)
    (hplanes : ∀ a ∈ normalizer (V : Set G), a ^ 2 = 1 →
      a ∉ centralizer (V : Set G) →
      Z ≤ ⁅V, zpowers a⁆ ∧ ⁅V, zpowers a⁆ = V ⊓ centralizer ({a} : Set G) ∧
        Nat.card (⁅V, zpowers a⁆ : Subgroup G) = 4)
    (g : G) (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hbound : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ k : G, V.map (MulAut.conj k).toMonoidHom = V.map (MulAut.conj g).toMonoidHom ∧
      Z ≤ ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj k).toMonoidHom⁆).map (MulAut.conj k).toMonoidHom =
        ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ∧
      Nat.card (⁅V, V.map (MulAut.conj k).toMonoidHom⁆ : Subgroup G) = 4 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := V.map (MulAut.conj g⁻¹).toMonoidHom
  let P := ⁅V, A⁆
  let Q := ⁅V, B⁆
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hback (U : Subgroup G) :
      (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = U := by
    rw [map_map]
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [he, map_id]
  have hforw (U : Subgroup G) :
      (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = U := by
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [he, map_id]
  have hPQ : P.map (MulAut.conj g⁻¹).toMonoidHom = Q := by
    dsimp [P, Q, A, B]
    rw [map_commutator]
    change ⁅B, (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom⁆ = ⁅V, B⁆
    rw [hback, commutator_comm]
  have hQP : Q.map (MulAut.conj g).toMonoidHom = P := by
    rw [← hPQ, hforw]
  have hQne : Q ≠ ⊥ := by
    intro he
    have hb : P = ⊥ := by rw [← hQP, he, map_bot]
    exact hcomm hb
  have hQV : Q ≤ V := by
    rw [← hPQ, ← hback V]
    exact map_mono (hbound.trans inf_le_right)
  have hQB : Q ≤ B := by
    rw [← hPQ]
    exact map_mono (hbound.trans inf_le_left)
  obtain ⟨hZP, hP⟩ := commutator_plane_of_involution_planes V Z A
    (le_normalizer_iff_commutator_le_left.mpr (hbound.trans inf_le_left))
    (le_normalizer_iff_commutator_le_right.mpr (hbound.trans inf_le_right)) hcomm hplanes
  obtain ⟨hZQ, hQ⟩ := commutator_plane_of_involution_planes V Z B
    (le_normalizer_iff_commutator_le_left.mpr hQV)
    (le_normalizer_iff_commutator_le_right.mpr hQB) hQne hplanes
  obtain ⟨l, hl, hlPQ⟩ := conjugate_planes_of_transitive_nonfixed V Z L hZ hLZ horbit
    P Q (hbound.trans inf_le_left) hQV hZP hZQ hP hQ
  have hcompose (U : Subgroup G) : U.map (MulAut.conj (g*l)).toMonoidHom =
      (U.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hA : V.map (MulAut.conj (g*l)).toMonoidHom = A := by
    have he : V.map (MulAut.conj l).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (hL hl)
    rw [hcompose, he]
  refine ⟨g*l, hA, ?_, ?_, ?_⟩
  · rwa [hA]
  · rw [hA]
    change P.map (MulAut.conj (g*l)).toMonoidHom = P
    rw [hcompose, hlPQ, hQP]
  · rwa [hA]
end Subgroup
