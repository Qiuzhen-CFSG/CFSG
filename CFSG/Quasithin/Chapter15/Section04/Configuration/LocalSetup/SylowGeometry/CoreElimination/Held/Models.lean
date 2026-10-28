module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Held
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.SingleComponentGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.ExceptionalG2
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center

/-!
# Separating the retained Held quotient from C.2.7 models

The concrete Held carrier has an element of order seventeen and a noncyclic
three-subgroup. These exclude the bounded alternating, binary linear,
symplectic and derived G₂ models, and the even-field rank-one models.
For full SL₃ over an even field, triviality of Held's center gives the
projective quotient. Its Sylow center has field order, whereas Held's has
order two; the resulting binary endpoint again lacks an element of order
seventeen. No Held order or multiplier is assumed.
Source: the model alternatives in C.2.7, pp.145--147, used for the retained
intrinsic Held case of 15.4.20.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.HeldModels
open ComponentElimination.OrdinaryReduction.RankOneModels
open BlockSieve.ExchangedCases

theorem seventeen_dvd_card : 17 ∣ Nat.card Held.He := by
  simpa only [Held.orderOf_ab] using orderOf_dvd_natCard (Held.a * Held.b)

theorem not_alternating {n : ℕ} (hn : n ≤ 8) :
    ¬ Nonempty (Held.He ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  have hd := seventeen_dvd_card.trans (Nat.card_congr e.toEquiv ▸
    (card_subgroup_dvd_card (alternatingGroup (Fin n))))
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hd
  have hb : n.factorial ∣ (8 : ℕ).factorial := Nat.factorial_dvd_factorial hn
  have := hd.trans hb
  norm_num at this

theorem not_even_rankOne {n : ℕ} (hn : 1 < n) :
    ¬ ClassicalGroup.IsPSL Held.He 2 (2 ^ n) := by
  intro hm
  by_cases he : n = 2
  · subst n
    exact sporadic_four_separation .he (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl ⟨2, by decide, rfl⟩) hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨A, hA, hnc⟩ := held_noncyclic_three_subgroup
  obtain ⟨P, hP⟩ := (hA.map e.toMonoidHom).exists_le_sylow
  have hf : 7 ≤ Nat.card F := by
    rw [hF]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n)
    omega
  let : IsCyclic P := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
    hF hf 3 (by decide) (by rw [hF]; exact (by decide : Nat.Coprime 3 2).pow_right n) P
  let : IsCyclic (A.map e.toMonoidHom) := Subgroup.isCyclic_of_le hP
  let f := A.equivMapOfInjective e.toMonoidHom e.injective
  exact hnc (isCyclic_of_injective f.toMonoidHom f.injective)

theorem not_full_linearThree {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    ¬ Nonempty (Held.He ≃* Matrix.SpecialLinearGroup (Fin 3) F) := by
  rintro ⟨e⟩
  have hc : center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := (Subgroup.centerCongr e).symm ⟨z, hz⟩ |>.property
    change e.symm z ∈ center Held.He at hh
    rw [Held.LocalPairs.center_eq_bot] at hh
    have hh' : e.symm z = 1 := hh
    exact e.symm.injective (hh'.trans (map_one e.symm).symm)
  let f := e.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F hc)
  let P : Sylow 2 Held.He := Classical.choice inferInstance
  have hs := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F hn hF f P
  rw [Held.LocalPairs.SylowGeometry.inner_center_card P] at hs
  have hcard : Nat.card F = 2 := hF.trans hs.symm
  have hd := seventeen_dvd_card
  rw [Nat.card_congr f.toEquiv] at hd
  have horder := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hcard] at horder
  norm_num [Fin.prod_univ_succ] at horder
  rw [horder] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.HeldModels
