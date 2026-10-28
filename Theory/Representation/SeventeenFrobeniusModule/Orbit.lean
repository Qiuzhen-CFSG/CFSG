module

public import Theory.Representation.AbelianWeightAutomizer
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# The eight-element orbit of a root eigenvector

In a faithful representation, the character weights of the cyclic subgroup of
order seventeen detect its generator. A nontrivial occurring eigenvalue has
order seventeen. The relation `r*x*r⁻¹=x²` makes translates by `r⁻¹` eigenvectors
with eigenvalues `μ^(2^i)`. The eight residues `2^i` modulo seventeen are distinct,
so these vectors are independent. In degree eight they form a basis, and `r^8=1`
closes the cycle. No irreducibility hypothesis is used.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript p.9; the Frobenius calculation used in Aschbacher--Smith K.2, p.453.
-/

open scoped IsMulCommutative
open Module
namespace Representation.SeventeenFrobeniusModule
variable {E G V : Type*} [Field E] [Group G]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V] [IsAlgClosed E]

private theorem root_eigenvector (ρ : Representation E G V) (hf : Function.Injective ρ)
    (x : G) (hx : orderOf x = 17) (h17 : (17 : E) ≠ 0) :
    ∃ μ : E, orderOf μ = 17 ∧ ∃ v : V, Module.End.HasEigenvector (ρ x) μ v := by
  let K := Subgroup.zpowers x
  let a : K := ⟨x, Subgroup.mem_zpowers x⟩
  let σ := ρ.comp K.subtype
  have ha : a ≠ 1 := by
    intro h
    have he : x = 1 := congrArg Subtype.val h
    simp [he] at hx
  have horder : (Nat.card K : E) ≠ 0 := by simpa [K, Nat.card_zpowers, hx] using h17
  have hc : ∃ χ : CharacterWeight σ, χ.val a ≠ 1 := by
    by_contra! hn
    apply ha
    apply eq_of_characterWeight_values σ (hf.comp Subtype.val_injective) horder
    intro χ
    simp [hn χ]
  obtain ⟨χ, hχ⟩ := hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.property
  let μ : E := χ.val a
  have hμ : μ ≠ 1 := fun h => hχ (Units.ext h)
  have ha17 : a ^ 17 = 1 := by
    apply Subtype.ext
    exact hx ▸ pow_orderOf_eq_one x
  have hμ17 : μ ^ 17 = 1 := by
    change (↑(χ.val a) : E) ^ 17 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ha17, map_one, Units.val_one]
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  refine ⟨μ, orderOf_eq_prime hμ17 hμ, v, ?_, hv0⟩
  exact (Submodule.mem_iInf _).mp hv a

omit [FiniteDimensional E V] [IsAlgClosed E] in
private theorem eigen_orbit (ρ : Representation E G V) (x r : G)
    (hrel : r * x * r⁻¹ = x ^ 2) {μ : E} {v : V}
    (hv : Module.End.HasEigenvector (ρ x) μ v) (n : ℕ) :
    Module.End.HasEigenvector (ρ x) (μ ^ (2 ^ n)) (ρ (r⁻¹ ^ n) v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hc : x * r⁻¹ = r⁻¹ * x ^ 2 := by
      rw [← hrel]
      group
    have hp : (ρ x) (ρ r⁻¹ (ρ (r⁻¹ ^ n) v)) =
        ρ r⁻¹ ((ρ x ^ 2) (ρ (r⁻¹ ^ n) v)) := by
      rw [← map_pow]
      change (ρ x * ρ r⁻¹) _ = (ρ r⁻¹ * ρ (x ^ 2)) _
      rw [← map_mul, ← map_mul, hc]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · rw [pow_succ', map_mul, Module.End.mul_apply, hp, ih.pow_apply 2, map_smul]
      rw [← pow_mul, pow_succ]
    · intro hz
      apply ih.2
      have hh := congrArg (ρ r) hz
      simpa [pow_succ', ← Module.End.mul_apply, ← map_mul] using hh

omit [IsAlgClosed E] in
private theorem eigenvalues_injective {μ : E} (hμ : orderOf μ = 17) :
    Function.Injective (fun i : Fin 8 => μ ^ (2 ^ i.val)) := by
  intro i j hij
  have hfin : IsOfFinOrder μ := orderOf_pos_iff.mp (by omega)
  have hm := hfin.pow_inj_mod.mp hij
  rw [hμ] at hm
  have hnumeric : Function.Injective (fun i : Fin 8 => 2 ^ i.val % 17) := by decide
  apply hnumeric
  exact hm

/-- A faithful degree-eight action of a literal `17:8` pair admits a basis
cyclically permuted by the inverse complement generator over a splitting field. -/
public theorem exists_cyclic_basis (ρ : Representation E G V) (hf : Function.Injective ρ)
    (hd : finrank E V = 8) (x r : G) (hx : orderOf x = 17)
    (hr : orderOf r = 8) (hrel : r * x * r⁻¹ = x ^ 2) (h17 : (17 : E) ≠ 0) :
    ∃ b : Basis (Fin 8) E V, ∀ i, ρ r⁻¹ (b i) = b (finRotate 8 i) := by
  obtain ⟨μ, hμ, v, hv⟩ := root_eigenvector ρ hf x hx h17
  have hi := Module.End.eigenvectors_linearIndependent' (ρ x) _ (eigenvalues_injective hμ)
    _ (fun i : Fin 8 => eigen_orbit ρ x r hrel hv i.val)
  let b : Basis (Fin 8) E V := basisOfLinearIndependentOfCardEqFinrank hi (by simp [hd])
  have hb (i : Fin 8) : b i = ρ (r⁻¹ ^ i.val) v := by
    simp [b]
  refine ⟨b, fun i => ?_⟩
  rw [hb, hb]
  have hr8 : r⁻¹ ^ 8 = 1 := by rw [inv_pow, ← hr, pow_orderOf_eq_one, inv_one]
  rw [← Module.End.mul_apply, ← map_mul, ← pow_succ']
  fin_cases i <;> norm_num [finRotate_apply, Fin.add_def, hr8]
end Representation.SeventeenFrobeniusModule
