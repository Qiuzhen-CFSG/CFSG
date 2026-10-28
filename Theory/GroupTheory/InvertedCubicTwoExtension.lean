module

public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognizing an inverted cubic two-extension

Suppose a finite group C has trivial two-core, a normal subgroup X of order
three, and a two-group quotient C/X. If some element of C inverts X, then
C is isomorphic to S₃, with X mapping to the actual alternating subgroup A₃.

Schur–Zassenhaus supplies a two-group complement to X. It is Sylow and has
index three. The inverter ensures the complement is nontrivial. The faithful
three-coset action, whose kernel is the two-core, then identifies C with S₃.
The subgroup correspondence follows from the cubic powers and cardinalities.

This is the intrinsic group input for the commuting inverted-cubic action in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.20,
external-X alternative (a), printed p.954 (PDF p.971), combined manuscript
of 1 March 2004. Each structural premise is explicit; an ambient centralizer
must satisfy these premises before this recognition can be used.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace InvertedCubicTwoExtension
variable {C : Type*} [Group C] [Finite C]

/-- A two-reduced inverted cubic extension by a two-group is S₃. -/
theorem exists_equiv (X : Subgroup C) [X.Normal]
    (hX : Nat.card X = 3) (hquot : IsPGroup 2 (C ⧸ X))
    (hcore : pCore 2 C = ⊥)
    (c : C) (hc : ∀ x ∈ X, c * x * c⁻¹ = x⁻¹) :
    Nonempty (C ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hcop : Nat.Coprime (Nat.card X) X.index := by
    obtain ⟨n, hn⟩ := hquot.exists_card_eq
    change Nat.Coprime (Nat.card X) (Nat.card (C ⧸ X))
    rw [hX, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨P, hP⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hi : P.index = 3 := hP.index_eq_card.trans hX
  have hp : IsPGroup 2 P := hquot.of_surjective hP.symm.QuotientMulEquiv.toMonoidHom
    hP.symm.QuotientMulEquiv.surjective
  let T : Sylow 2 C := hp.toSylow (by rw [hi]; decide)
  have hPne : P ≠ ⊥ := by
    intro heq
    have htop : X = ⊤ := by
      have hh := hP.sup_eq_top
      simpa only [heq, sup_bot_eq] using hh
    let : IsCyclic X := isCyclic_of_prime_card hX
    have hnon : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let := hnon
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    have hcx : c * x.val = x.val * c := by
      have hh := mul_comm (⟨c, by rw [htop]; trivial⟩ : X) x
      exact congrArg Subtype.val hh
    have hinv : x.val = x.val⁻¹ := by
      have hh := hc x x.property
      rwa [hcx, mul_inv_cancel_right] at hh
    have htwo : x ^ 2 = 1 := by
      apply Subtype.ext
      change x.val ^ 2 = 1
      rw [pow_two]
      calc
        _ = x.val⁻¹ * x.val := congrArg (· * x.val) hinv
        _ = 1 := inv_mul_cancel _
    have hthree : x ^ 3 = 1 := by
      simpa only [hX] using (pow_card_eq_one' (x := x))
    have hone : x = 1 := by
      have hh := hthree
      rw [pow_succ, htwo, one_mul] at hh
      exact hh
    exact hx hone
  have hproper : pCore 2 C < (T : Subgroup C) := by
    rw [hcore]
    exact bot_lt_iff_ne_bot.mpr hPne
  obtain ⟨e⟩ := sylow_index_three_core_quotient T hi hproper
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot)).symm.trans e⟩

/-- The order-three subgroup is identified with the actual alternating subgroup. -/
theorem exists_equiv_preserving_cubic (X : Subgroup C) [X.Normal]
    (hX : Nat.card X = 3) (hquot : IsPGroup 2 (C ⧸ X))
    (hcore : pCore 2 C = ⊥)
    (c : C) (hc : ∀ x ∈ X, c * x * c⁻¹ = x⁻¹) :
    ∃ e : C ≃* Equiv.Perm (Fin 3), X.map e.toMonoidHom = alternatingGroup (Fin 3) := by
  obtain ⟨e⟩ := exists_equiv X hX hquot hcore c hc
  refine ⟨e, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have h : ∀ g : Equiv.Perm (Fin 3), g ^ 3 = 1 → Equiv.Perm.sign g = 1 := by
      decide +kernel
    apply h
    have hx3 : x ^ 3 = 1 := by
      have hh : (⟨x, hx⟩ : X) ^ 3 = 1 := by
        simpa only [hX] using (pow_card_eq_one' (x := (⟨x, hx⟩ : X)))
      exact congrArg Subtype.val hh
    simp only [← map_pow, hx3, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hX,
      nat_card_alternatingGroup]
    norm_num

end InvertedCubicTwoExtension
