module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-!
# The quotient associated to a Sylow subgroup of index three

If a Sylow two-subgroup has index three and properly contains the two-core,
the quotient by the two-core is the symmetric group on three letters.
The coset action has kernel equal to the two-core; its faithful quotient
has order dividing six and greater than three.

Source/application: Parrott, *A characterization of the Tits' simple group*
(1972), p.677, the order and quotient deductions in Lemma 6.
-/

open Subgroup

/-- The faithful three-coset action identifies the quotient by the two-core. -/
public theorem sylow_index_three_core_quotient {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (hproper : pCore 2 G < (T : Subgroup G)) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  classical
  let K := pCore 2 G
  have hcore : (T : Subgroup G).normalCore = K := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, T.isPGroup'.to_le (T : Subgroup G).normalCore_le⟩
    · exact normal_le_normalCore.mpr (pCore_isPGroup.le_sylow_of_normal T)
  let points := G ⧸ (T : Subgroup G)
  let action : G →* Equiv.Perm points := MulAction.toPermHom G points
  have hker : action.ker = K :=
    ((T : Subgroup G).normalCore_eq_ker).symm.trans hcore
  let quotientAction := QuotientGroup.lift K action hker.ge
  have hinj : Function.Injective quotientAction :=
    (QuotientGroup.injective_lift_iff K action hker.ge).mpr hker.symm
  have hpoints : Nat.card points = 3 := hi
  let _ := Fintype.ofFinite points
  have hperm : Nat.card (Equiv.Perm points) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hpoints]
    decide
  have hdiv : Nat.card (G ⧸ K) ∣ 6 := by
    rw [← hperm]
    exact card_dvd_of_injective quotientAction hinj
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKcard : Nat.card K < Nat.card (T : Subgroup G) := by
    apply lt_of_not_ge
    intro hcard
    exact hproper.ne (eq_of_le_of_card_ge hproper.le hcard)
  have hcount := K.index_mul_card
  change Nat.card (G ⧸ K) * Nat.card K = Nat.card G at hcount
  have hTcount := (T : Subgroup G).index_mul_card
  rw [hi] at hTcount
  have hlarge : 3 < Nat.card (G ⧸ K) := by nlinarith
  have hcard : Nat.card (G ⧸ K) = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    interval_cases hc : Nat.card (G ⧸ K) <;> norm_num [hc] at *
  have hbij : Function.Bijective quotientAction :=
    (Nat.bijective_iff_injective_and_card quotientAction).mpr ⟨hinj, hcard.trans hperm.symm⟩
  let ep : points ≃ Fin 3 := (Finite.equivFin points).trans (finCongr hpoints)
  exact ⟨(MulEquiv.ofBijective quotientAction hbij).trans (Equiv.permCongrHom ep)⟩
