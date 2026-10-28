module
public import Theory.GroupTheory.CubicNormalizerNine

/-!
# Cubics supplement a Sylow subgroup in a two-by-six group

When D/O₂(D) has order six, a Sylow two-subgroup has index three.
An element of order three lies outside that Sylow subgroup, and prime
index forces their join to be D.

Source application: Y=⟨T_Y,P∩Y₀⟩ and hence I=⟨L₁T,P⟩ in
Aschbacher–Smith, proof of 14.7.32, printed p.1058.
-/

public noncomputable section
open Subgroup
namespace Sylow
variable {D : Type*} [Group D] [Finite D]
theorem sup_cubic_eq_top_of_twoCore_quotient_six (S : Sylow 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 6)
    (x : D) (hx : orderOf x = 3) : (S : Subgroup D) ⊔ zpowers x = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hi : (R : Subgroup (D ⧸ pCore 2 D)).index = (S : Subgroup D).index :=
    (S : Subgroup D).index_map_eq (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
  have hr : Nat.card R = 2 := by rw [R.card_eq_multiplicity,hc]; decide +kernel
  have hs3 : (S : Subgroup D).index = 3 := by
    have hh := (R : Subgroup (D ⧸ pCore 2 D)).index_mul_card
    rw [hi,hr,hc] at hh
    omega
  let B := (S : Subgroup D) ⊔ zpowers x
  have hd : B.index ∣ 3 := hs3 ▸ index_dvd_of_le (show (S : Subgroup D) ≤ B from le_sup_left)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
  · exact index_eq_one.mp he
  · have hh := relIndex_mul_index (show (S : Subgroup D) ≤ B from le_sup_left)
    rw [he,hs3] at hh
    have hrel : (S : Subgroup D).relIndex B = 1 := by omega
    have hxS : x ∈ S := (relIndex_eq_one.mp hrel) (mem_sup_right (mem_zpowers x))
    have hcop := S.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨x,hxS⟩
    rw [Subgroup.orderOf_mk,hx] at hcop
    norm_num at hcop
end Sylow
