module

public import Theory.PGroupCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A normal order-two actor on an irreducible abelian subgroup

Suppose E = AT, where A is normal abelian, T acts irreducibly on A,
and O₂(E)=1. An order-two subgroup V normalized by T inverts A.
Indeed C_A(V) is T-invariant. If it is all of A, V is normal in E,
contrary to O₂(E)=1. If it is trivial, the product of any a with its
conjugate by the nonidentity element of V is fixed, hence is the identity.

Source application: Aschbacher–Smith, Lemma 8.2.7, printed p.718
(PDF p.735 in refs/quasithin.pdf). The application uses E=H/O₂(H).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {E : Type*} [Group E]

/-- The nonidentity element of a T-normalized subgroup of order two inverts
the normal abelian irreducible factor of a group with trivial two-core. -/
theorem exists_inverter_of_card_two (A T V : Subgroup E) [A.Normal] [IsMulCommutative A]
    (hgen : A ⊔ T = ⊤) (hTV : T ≤ normalizer (V : Set E))
    (hcard : Nat.card V = 2) (hcore : pCore 2 E = ⊥)
    (hirr : ∀ D : Subgroup E, D ≤ A → T ≤ normalizer (D : Set E) → D = ⊥ ∨ D = A) :
    ∃ v : V, ∀ a ∈ A, (v : E) * a * (v : E)⁻¹ = a⁻¹ := by
  let C := A ⊓ centralizer (V : Set E)
  have hn : T ≤ normalizer (C : Set E) :=
    (le_inf (by rw [A.normalizer_eq_top]; exact le_top)
      (hTV.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf
  have hC : C = ⊥ := by
    rcases hirr C inf_le_left hn with h | h
    · exact h
    have hAV : A ≤ centralizer (V : Set E) := h ▸ inf_le_right
    have hNV : (⊤ : Subgroup E) ≤ normalizer (V : Set E) := by
      rw [← hgen]
      exact sup_le (hAV.trans (Subgroup.centralizer_le_normalizer _)) hTV
    let _ : V.Normal := normalizer_eq_top_iff.mp (top_unique hNV)
    have hp : V ≤ pCore 2 E := le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa using hcard)⟩
    have hv0 : V = ⊥ := bot_unique (hcore ▸ hp)
    simp [hv0] at hcard
  obtain ⟨v, hv, hall⟩ := (Nat.card_eq_two_iff' (1 : V)).mp hcard
  refine ⟨v, ?_⟩
  have hv2 : (v : E) * (v : E) = 1 := by
    have hh := pow_card_eq_one' (x := v)
    rw [hcard, pow_two] at hh
    exact congrArg Subtype.val hh
  intro a ha
  have hb : (v : E) * a * (v : E)⁻¹ ∈ A := Subgroup.Normal.conj_mem inferInstance a ha v
  have hab : a * ((v : E) * a * (v : E)⁻¹) = ((v : E) * a * (v : E)⁻¹) * a :=
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨_, hb⟩)
  have hd : (v : E) * a * (v : E)⁻¹ * a ∈ C := by
    refine ⟨A.mul_mem hb ha, mem_centralizer_iff.mpr ?_⟩
    intro w hw
    by_cases hw1 : (⟨w, hw⟩ : V) = 1
    · have : w = 1 := congrArg Subtype.val hw1
      simp [this]
    · have : w = (v : E) := congrArg Subtype.val (hall ⟨w, hw⟩ hw1)
      subst w
      apply mul_right_cancel (b := (v : E)⁻¹)
      calc
        (v : E) * ((v : E) * a * (v : E)⁻¹ * a) * (v : E)⁻¹ =
            a * ((v : E) * a * (v : E)⁻¹) := by
              have hvi : (v : E)⁻¹ = (v : E) := inv_eq_of_mul_eq_one_left hv2
              rw [hvi]
              simp only [← mul_assoc, hv2, one_mul]
        _ = ((v : E) * a * (v : E)⁻¹ * a) * (v : E) * (v : E)⁻¹ := by
          simpa only [mul_inv_cancel_right] using hab
  have he : (v : E) * a * (v : E)⁻¹ * a = 1 := by simpa only [hC, mem_bot] using hd
  exact mul_eq_one_iff_eq_inv.mp he
end Subgroup
