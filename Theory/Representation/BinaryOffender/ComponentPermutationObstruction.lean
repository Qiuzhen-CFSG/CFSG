module

public import Theory.Representation.BinaryOffender.ComponentDisplacement
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Four-group reduction for the component-permutation obstruction

For an elementary abelian subgroup `A`, let `C = C_A([V,A])`. If `a ∈ A`
moves `L` and `c ∈ C` is distinct from `1` and `a`, then `B = ⟨a,c⟩`
is a four-group satisfying `[V,a,B] = 0`. If `C_C(L) = 1` and either
`C = A` or `C` normalizes `L`, then `C_B(L) = 1` as well.

This constructs the actual subgroup required by Aschbacher's quadratic
four-group theorem. It does not prove that theorem or the final
component-normalization assertion: the cyclic alternative and the subsequent
natural tensor-module obstruction remain separate mathematical inputs.

Source: GLS, *The Classification of the Finite Simple Groups*, vol. 2,
Theorem 26.24, the construction after Step 2 and the proof of Step 4.
-/

@[expose] public section
namespace Representation.BinaryOffender

open Subgroup
open scoped IsMulCommutative

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Failure to normalize a component is witnessed by an involution whose
conjugate component commutes with the original one. This uses unrestricted
quasisimple component calculus, with no assumption of ambient normality. -/
theorem exists_moving_component_involution {A L : Subgroup G}
    (hA : IsElementaryTwo A) (hL : Theory.GroupTheory.IsComponent G L)
    (hAN : ¬ A ≤ normalizer (L : Set G)) :
    ∃ a ∈ A, orderOf a = 2 ∧ a ∉ normalizer (L : Set G) ∧
      L.map (MulAut.conj a).toMonoidHom ≠ L ∧
      ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
  classical
  obtain ⟨a, ha, haN⟩ : ∃ a ∈ A, a ∉ normalizer (L : Set G) := by
    by_contra h
    apply hAN
    intro a ha
    exact by_contra fun haN => h ⟨a, ha, haN⟩
  let _ : IsElementaryAbelian 2 A := hA.2
  have ha1 : a ≠ 1 := fun h => haN (h ▸ (normalizer (L : Set G)).one_mem)
  have hmove : L.map (MulAut.conj a).toMonoidHom ≠ L :=
    fun h => haN (mem_normalizer_iff_map_conj_eq.mpr h)
  exact ⟨a, ha, orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) ha1,
    haN, hmove, hL.commutator_eq_bot_of_ne (hL.map_conj a) (Ne.symm hmove)⟩

private theorem binary_neg (v : V) : -v = v := by
  have h : v + v = 0 := by
    calc
      v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
      _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
  exact neg_eq_of_add_eq_zero_left h

/-- In characteristic two an involution fixes each of its own displacements. -/
theorem involution_fixes_displacement {a : G} (ha : a * a = 1) (v : V) :
    ρ a (ρ a v - v) = ρ a v - v := by
  rw [map_sub]
  have h : ρ a (ρ a v) = v := by
    change (ρ a * ρ a) v = v
    rw [← map_mul, ha, map_one]
    rfl
  rw [h, sub_eq_add_neg, sub_eq_add_neg, binary_neg, binary_neg, add_comm]

/-- The concrete pair used in GLS 26.24 satisfies all the local four-group
hypotheses. No normalization of `A`, or component classification, is assumed. -/
theorem displacement_pair_fourGroup {A L : Subgroup G}
    (hA : IsElementaryTwo A) {a c : G} (ha : a ∈ A)
    (haN : a ∉ normalizer (L : Set G))
    (hc : c ∈ displacementCentralizer ρ A) (hc1 : c ≠ 1) (hca : c ≠ a)
    (hcent : displacementCentralizer ρ A ⊓ centralizer (L : Set G) = ⊥)
    (halt : displacementCentralizer ρ A = A ∨
      displacementCentralizer ρ A ≤ normalizer (L : Set G)) :
    let B := closure ({a, c} : Set G)
    B ≤ A ∧ IsElementaryTwo B ∧ Nat.card B = 4 ∧ a ∈ B ∧ c ∈ B ∧
      (∀ b ∈ B, ∀ v : V, ρ b (ρ a v - v) = ρ a v - v) ∧
      B ⊓ centralizer (L : Set G) = ⊥ := by
  let _ : IsElementaryAbelian 2 A := hA.2
  have ha2 : a * a = 1 := by
    simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hc2 : c * c = 1 := by
    simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc.1
  have hac : Commute a c := by
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm
      (⟨a, ha⟩ : A) ⟨c, hc.1⟩)
  have ha1 : a ≠ 1 := fun h => haN (h ▸ (normalizer (L : Set G)).one_mem)
  let B := closure ({a, c} : Set G)
  have hBA : B ≤ A := (closure_le _).mpr (by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ha
    · exact (Set.mem_singleton_iff.mp hx) ▸ hc.1)
  have hab : a ∈ B := subset_closure (by simp)
  have hcb : c ∈ B := subset_closure (by simp)
  have hB0 : B ≠ ⊥ := by
    intro h
    exact ha1 (mem_bot.mp (h ▸ hab))
  have hfour : IsKleinFour B := isKleinFour_closure_pair a c ha2 hc2 ha1 hc1
    (Ne.symm hca) hac
  let _ := hfour
  refine ⟨hBA, hA.of_le hBA hB0, IsKleinFour.card_four, hab, hcb, ?_, ?_⟩
  · intro b hb v
    rcases (mem_closure_pair_iff a c ha2 hc2 hac b).mp hb with rfl | rfl | rfl | rfl
    · simp
    · exact involution_fixes_displacement ρ ha2 v
    · exact hc.2 a ha v
    · rw [map_mul]
      change ρ a (ρ c (ρ a v - v)) = _
      rw [hc.2 a ha v, involution_fixes_displacement ρ ha2 v]
  · apply (eq_bot_iff_forall _).mpr
    rintro b ⟨hb, hbcent⟩
    have hbC : b ∈ displacementCentralizer ρ A := by
      rcases halt with heq | hCN
      · rw [heq]
        exact hBA hb
      · have hbN := centralizer_le_normalizer (L : Set G) hbcent
        rcases (mem_closure_pair_iff a c ha2 hc2 hac b).mp hb with rfl | rfl | rfl | rfl
        · exact (displacementCentralizer ρ A).one_mem
        · exact (haN hbN).elim
        · exact hc
        · exact (haN ((normalizer (L : Set G)).mul_mem_cancel_right (hCN hc) |>.mp hbN)).elim
    exact mem_bot.mp (hcent ▸ (show b ∈ displacementCentralizer ρ A ⊓
      centralizer (L : Set G) from ⟨hbC, hbcent⟩))

/-- Every moving involution either generates the whole nontrivial replacement
subgroup, or belongs to a concrete quadratic four-group with trivial local
centralizer. The cyclic alternative still needs the order-two offender argument. -/
theorem displacement_cyclic_or_exists_fourGroup {A L : Subgroup G}
    (hA : IsElementaryTwo A) {a : G} (ha : a ∈ A)
    (haN : a ∉ normalizer (L : Set G))
    (hC0 : displacementCentralizer ρ A ≠ ⊥)
    (hcent : displacementCentralizer ρ A ⊓ centralizer (L : Set G) = ⊥)
    (halt : displacementCentralizer ρ A = A ∨
      displacementCentralizer ρ A ≤ normalizer (L : Set G)) :
    displacementCentralizer ρ A = zpowers a ∨
      ∃ c ∈ displacementCentralizer ρ A, c ≠ 1 ∧ c ≠ a ∧
        ∃ B : Subgroup G, B = closure ({a, c} : Set G) ∧
          B ≤ A ∧ IsElementaryTwo B ∧ Nat.card B = 4 ∧ a ∈ B ∧ c ∈ B ∧
          (∀ b ∈ B, ∀ v : V, ρ b (ρ a v - v) = ρ a v - v) ∧
          B ⊓ centralizer (L : Set G) = ⊥ := by
  classical
  by_cases hex : ∃ c ∈ displacementCentralizer ρ A, c ≠ 1 ∧ c ≠ a
  · obtain ⟨c, hc, hc1, hca⟩ := hex
    exact Or.inr ⟨c, hc, hc1, hca, closure ({a, c} : Set G), rfl,
      displacement_pair_fourGroup ρ hA ha haN hc hc1 hca hcent halt⟩
  · left
    have hcases : ∀ c ∈ displacementCentralizer ρ A, c = 1 ∨ c = a := by
      intro c hc
      by_cases h : c = 1
      · exact Or.inl h
      · exact Or.inr (by_contra fun hca => hex ⟨c, hc, h, hca⟩)
    have hCa : displacementCentralizer ρ A ≤ zpowers a := by
      intro c hc
      rcases hcases c hc with rfl | rfl
      · exact (zpowers a).one_mem
      · exact mem_zpowers _
    apply le_antisymm hCa
    apply zpowers_le.mpr
    obtain ⟨c, hc1⟩ := ne_bot_iff_exists_ne_one.mp hC0
    have hcne : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
    rcases hcases c c.property with h | h
    · exact (hcne h).elim
    · exact h ▸ c.property

end Representation.BinaryOffender
