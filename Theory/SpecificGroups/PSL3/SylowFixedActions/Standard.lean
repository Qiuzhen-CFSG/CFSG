module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.Model
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.ScalarLift
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.NormalForm
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.TwoSubgroup
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.MatrixFixer
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# No faithful standard four-group action fixing a Sylow two-subgroup of PSL₃

For a prime p congruent to five modulo eight, choose a unit of order four.
The diagonal tests and coordinate interchange lie in a two-subgroup. Embed
it in a Sylow subgroup and conjugate that subgroup to the prescribed Sylow.
Standardness is preserved because the conjugating automorphism is inner.

The matrix calculation puts every transported actor in the cyclic image of
`diag(1,1,t)` and excludes every graph coset. A faithful elementary abelian
group of order four would therefore be cyclic, contradicting its exponent.
The cubic scalar kernel is handled by `Standard.ScalarLift`; no trivial-center,
group-order, simplicity, or arbitrary-automorphism-coverage premise is needed.

Source: GLS3, §2.7, `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115, and the
linear alternatives of Aschbacher–Smith F.6.18(10)–(11), printed pp.309–310,
used in the component inspection in 15.4.18, printed pp.1162–1163.
The separate source assembly must still discharge standardness.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.SylowFixedActions.Standard
open Matrix.PSL3.OuterSolvable

/-- The prime-field congruence supplies the fourth root needed by the tests. -/
theorem exists_unit_order_four (p : ℕ) [Fact p.Prime] (hp : p % 8 = 5) :
    ∃ u : (ZMod p)ˣ, orderOf u = 4 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hc : orderOf g = p - 1 := by
    rw [hg, Nat.card_units, Nat.card_zmod]
  refine ⟨g ^ (orderOf g / 4), orderOf_pow_orderOf_div ?_ ?_⟩
  · rw [hc]
    omega
  · rw [hc]
    exact Nat.dvd_of_mod_eq_zero (by omega)

/-- Sylow conjugacy transfers the three explicit tests to any Sylow subgroup.
The two matrix calculations and the two-subgroup placement are explicit here. -/
theorem not_injective_of_test_calculations (p : ℕ) [Fact p.Prime]
    (P : Sylow 2 PSL(3, ZMod p)) (u : (ZMod p)ˣ)
    (hplacement : ∃ Q : Subgroup PSL(3, ZMod p),
      IsPGroup 2 Q ∧ testSet (ZMod p) u ⊆ Q)
    (hlinear : ∀ g : GL (Fin 3) (ZMod p),
      (∀ x ∈ testSet (ZMod p) u, linearConj (ZMod p) g x = x) →
        linearConj (ZMod p) g ∈ (fixerAction (ZMod p)).range)
    (hgraph : ∀ g : GL (Fin 3) (ZMod p),
      ¬ ∀ x ∈ testSet (ZMod p) u, (linearConj (ZMod p) g * graph (ZMod p)) x = x)
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (ρ : A →* MulAut PSL(3, ZMod p))
    (hstandard : ∀ a, ρ a ∈ standard (ZMod p))
    (hfix : ∀ a, ∀ x : P, ρ a x = x) : ¬ Function.Injective ρ := by
  obtain ⟨Q, hQ, htests⟩ := hplacement
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3, ZMod p) S P
  let e := MulAut.conj g
  have hm : (S : Subgroup PSL(3, ZMod p)).map e.toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  let σ : A →* MulAut PSL(3, ZMod p) := (MulAut.congr e.symm).toMonoidHom.comp ρ
  have he : e ∈ standard (ZMod p) := inner_le_standard (ZMod p) ⟨g, rfl⟩
  have hσstandard (a : A) : σ a ∈ standard (ZMod p) := by
    have heq : σ a = e⁻¹ * ρ a * e := by ext x; rfl
    rw [heq]
    exact (standard (ZMod p)).mul_mem
      ((standard (ZMod p)).mul_mem ((standard (ZMod p)).inv_mem he) (hstandard a)) he
  have hσfix (a : A) (x : PSL(3, ZMod p)) (hx : x ∈ testSet (ZMod p) u) : σ a x = x := by
    change e.symm (ρ a (e x)) = x
    have hxP : e x ∈ (P : Subgroup PSL(3, ZMod p)) := by
      rw [← hm]
      exact Subgroup.mem_map_of_mem e.toMonoidHom (hQS (htests hx))
    rw [hfix a ⟨e x, hxP⟩, e.symm_apply_apply]
  have hσrange (a : A) : σ a ∈ (fixerAction (ZMod p)).range := by
    obtain ⟨m, h | h⟩ := normal_form p (σ a) (hσstandard a)
    · rw [h]
      exact hlinear m (h ▸ hσfix a)
    · exact (hgraph m (h ▸ hσfix a)).elim
  intro hinj
  let τ := σ.codRestrict (fixerAction (ZMod p)).range hσrange
  have hτ : Function.Injective τ := by
    intro a b hab
    apply hinj
    apply (MulAut.congr e.symm).injective
    exact congrArg Subtype.val hab
  let := fixerAction_range_isCyclic (ZMod p)
  let : IsCyclic A := isCyclic_of_injective τ hτ
  have hc := IsElementaryAbelian.exponent_dvd_p 2 A
  rw [IsCyclic.exponent_eq_card, hA] at hc
  norm_num at hc

/-- A standard action of a four-group on PSL₃(p), for p congruent to five
modulo eight, cannot be faithful while fixing a Sylow two-subgroup pointwise. -/
theorem not_injective (p : ℕ) [Fact p.Prime] (hp : p % 8 = 5)
    (P : Sylow 2 PSL(3, ZMod p))
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (ρ : A →* MulAut PSL(3, ZMod p))
    (hstandard : ∀ a, ρ a ∈ standard (ZMod p))
    (hfix : ∀ a, ∀ x : P, ρ a x = x) : ¬ Function.Injective ρ := by
  obtain ⟨u, hu⟩ := exists_unit_order_four p hp
  have hpow : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  exact not_injective_of_test_calculations p P u
    (exists_two_subgroup_containing_tests (ZMod p) u hpow)
    (linear_fixes_tests_mem_range u hu) (graph_not_fixes_tests u hu)
    hA ρ hstandard hfix

end Matrix.PSL3.SylowFixedActions.Standard
