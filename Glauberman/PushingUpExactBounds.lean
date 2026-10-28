module
public import Glauberman.PushingUpOmegaFixedIndex
/-!
# Exact Sylow class and exponent from the source bounds

The original natural omega action makes the Sylow subgroup nonabelian: its
fixed index is at least four, whereas an abelian Sylow would centralize its
core omega. Consequently class at most two is exactly two. If every fourth
power is one, a smaller exponent would divide two and again force the Sylow
to be abelian. This removes exactness obligations from the Main Hypothesis
structure proof without assuming exponent four from class two alone.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem B, printed p.28.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_sylow_noncommutative
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) : ¬ IsMulCommutative S := by
  intro hs
  have hi : (pCore 2 H).relIndex (S : Subgroup H) = 4 := by
    rw [relIndex,index_eq_card]
    exact (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four hF S hu K e).2
  have hSQ : ¬ (S : Subgroup H) ≤ pCore 2 H := by
    intro h
    have he := relIndex_eq_one.mpr h
    rw [hi] at he
    contradiction
  have hVS : omegaCenterIn (pCore 2 H) ≤ (S : Subgroup H) :=
    fun _ hx => pCore_isPGroup.le_sylow_of_normal S ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hSC : (S : Subgroup H) ≤ centralizer (omegaCenterIn (pCore 2 H) : Set H) :=
    (le_centralizer_iff_isMulCommutative.mpr hs).trans (centralizer_le hVS)
  have hVC : omegaCenterIn (pCore 2 H) ≤ centralizer ((S : Subgroup H) : Set H) :=
    le_centralizer_iff.mp hSC
  have hl := (original_psl2_four_omega_fixedIndex_data hF S hu K e hf hno).1
    (S : Subgroup H) le_rfl hSQ
  rw [inf_eq_left.mpr hVC,relIndex_self] at hl
  omega

theorem original_psl2_four_exact_of_bounds
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hclass : Group.nilpotencyClass S ≤ 2)
    (hpow : ∀ s : S, s ^ 4 = 1) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 := by
  have hn := original_psl2_four_sylow_noncommutative hF S hu K e hf hno
  let _ := S.isPGroup'.isNilpotent
  have hcl : Group.nilpotencyClass S = 2 := by
    have he : ¬ Group.nilpotencyClass S ≤ 1 :=
      fun h => hn (Group.IsNilpotent.nilpotencyClass_le_one_iff.mp h)
    omega
  refine ⟨hcl,?_⟩
  have hd : Monoid.exponent S ∣ 4 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  have hle : Monoid.exponent S ≤ 4 := Nat.le_of_dvd (by decide) hd
  by_contra hne
  have hd2 : Monoid.exponent S ∣ 2 := by
    interval_cases h : Monoid.exponent S <;> simp_all
  apply hn
  exact ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun g => dvd_trans (Monoid.order_dvd_exponent g) hd2) a b).eq⟩⟩
end Glauberman
