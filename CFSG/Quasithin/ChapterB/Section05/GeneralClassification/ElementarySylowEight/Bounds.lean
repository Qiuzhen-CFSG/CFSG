module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary Sylow subgroups of order at most eight

These bounds retain all two-subgroups, so they pass to literal subgroups and
surjective images. They are used to inspect the complete B.5 alternatives in
the original opposite-plane argument of Aschbacher--Smith 12.7.5, p.841.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight

def Bound (D : Type*) [Group D] : Prop :=
  ∀ P : Subgroup D, IsPGroup 2 P → IsElementaryAbelian 2 P ∧ Nat.card P ≤ 8

variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

theorem of_sylows
    (he : ∀ P : Sylow 2 D, IsElementaryAbelian 2 P)
    (hc : ∀ P : Sylow 2 D, Nat.card P ≤ 8) : Bound D := by
  intro P hp
  obtain ⟨S,hPS⟩ := hp.exists_le_sylow
  let : IsElementaryAbelian 2 S := he S
  exact ⟨IsElementaryAbelian.of_injective (inclusion hPS) (inclusion_injective hPS),
    (card_le_of_le hPS).trans (hc S)⟩

omit [Finite D] in
theorem Bound.sylow (h : Bound D) (P : Sylow 2 D) :
    IsElementaryAbelian 2 P ∧ Nat.card P ≤ 8 := h P P.isPGroup'

omit [Finite D] [Finite E] in
theorem Bound.of_injective (h : Bound D) (f : E →* D) (hf : Function.Injective f) :
    Bound E := by
  intro P hp
  obtain ⟨he,hc⟩ := h (P.map f) (hp.map f)
  let : IsElementaryAbelian 2 (P.map f) := he
  let e := P.equivMapOfInjective f hf
  exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).le.trans hc⟩

theorem Bound.of_surjective (h : Bound D) (f : D →* E) (hf : Function.Surjective f) :
    Bound E := by
  apply of_sylows
  · intro P
    obtain ⟨S,rfl⟩ := Sylow.mapSurjective_surjective hf 2 P
    let : IsElementaryAbelian 2 S := (h.sylow S).1
    exact IsElementaryAbelian.map f
  · intro P
    obtain ⟨S,rfl⟩ := Sylow.mapSurjective_surjective hf 2 P
    exact (Nat.le_of_dvd (Nat.card_pos (α := S)) (card_map_dvd _ _)).trans (h.sylow S).2

theorem Bound.two_power_le (h : Bound D) {n : ℕ} (hd : 2 ^ n ∣ Nat.card D) : n ≤ 3 := by
  let S : Sylow 2 D := default
  have hs := S.pow_dvd_card_of_pow_dvd_card hd
  have hh : 2 ^ n ≤ 2 ^ 3 :=
    (Nat.le_of_dvd (Nat.card_pos (α := S)) hs).trans (h.sylow S).2
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh

theorem Bound.not_sixteen_dvd (h : Bound D) : ¬ 16 ∣ Nat.card D := by
  intro hd
  have := h.two_power_le (n := 4) hd
  omega

omit [Finite D] in
theorem Bound.no_order_four (h : Bound D) (x : D) (hx : orderOf x = 4) : False := by
  have hc : Nat.card (zpowers x) = 4 := (Nat.card_zpowers x).trans hx
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 2) hc
  let : IsElementaryAbelian 2 (zpowers x) := (h _ hp).1
  have hs : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x (mem_zpowers x)
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hx] at hd
  norm_num at hd

theorem no_alternating_six (h : Bound (alternatingGroup (Fin 6))) : False := by
  apply h.no_order_four AlternatingSix.ShadowLocal.dihedralRotation
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4)
  · decide +kernel
  · intro p hp hd
    have hp2 : p = 2 := by
      have hp' := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd)
      exact (Nat.dvd_prime Nat.prime_two).mp hp' |>.resolve_left hp.ne_one
    subst p
    decide +kernel

theorem no_alternating_seven (h : Bound (alternatingGroup (Fin 7))) : False := by
  let x : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  apply h.no_order_four x
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4)
  · decide +kernel
  · intro p hp hd
    have hp2 : p = 2 := by
      have hp' := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd)
      exact (Nat.dvd_prime Nat.prime_two).mp hp' |>.resolve_left hp.ne_one
    subst p
    decide +kernel

theorem no_psl_three_two (h : Bound Matrix.PSL3Two.PSL) : False := by
  let P : Sylow 2 Matrix.PSL3Two.PSL := default
  let : IsElementaryAbelian 2 P := (h.sylow P).1
  exact Matrix.PSL3Two.not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => Commute.all a b) (MonoidHom.id _) Function.injective_id

end CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
