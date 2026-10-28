module
public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A vector detecting a cyclic linear action

The polynomial module attached to a cyclic generator has a vector with the
same annihilator as the entire module, by the structure theorem for finitely
generated modules over a PID. Consequently its stabilizer is the action
kernel. A faithful cyclic linear group therefore has order at most the
cardinality of its module. No coprimality assumption is needed.

This supplies the cyclic-torus kernel argument in DGS, *Groups and Graphs*
(1985), proof of (8.3), p.136, on the literal quotient omega-center.
-/

public section
open Polynomial
open Subgroup
namespace Representation
variable {K C V : Type*} [Field K] [Group C] [Finite C] [IsCyclic C]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A cyclic linear action has a vector whose stabilizer is its full kernel. -/
theorem exists_cyclic_detecting_vector (ρ : Representation K C V) :
    ∃ v : V, ∀ g : C, ρ g v = v → ρ g = 1 := by
  obtain ⟨c,hc⟩ := IsCyclic.exists_generator (α := C)
  let T := ρ c
  let M := Module.AEval K V T
  obtain ⟨v,hv⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X] M
  refine ⟨(Module.AEval.of K V T).symm v,?_⟩
  intro g hg
  obtain ⟨n,rfl⟩ := (mem_powers_iff_mem_zpowers.mpr (hc g))
  have hpoly : X^n - 1 ∈ Module.annihilator K[X] M := by
    rw [←hv]
    change ((X : K[X])^n - 1) • v = 0
    apply (Module.AEval.of K V T).symm.injective
    change (aeval T ((X : K[X])^n - 1)) ((Module.AEval.of K V T).symm v) = 0
    simpa only [map_sub, map_one, aeval_X_pow, LinearMap.sub_apply,
      Module.End.one_apply, T, ←map_pow, sub_eq_zero] using hg
  rw [Module.AEval.annihilator_eq_ker_aeval] at hpoly
  change aeval T (X^n - 1) = 0 at hpoly
  simpa only [map_sub, aeval_X_pow, map_one, sub_eq_zero, T, ←map_pow] using hpoly

/-- A faithful cyclic linear group has order at most the size of its module. -/
theorem cyclic_card_le (ρ : Representation K C V) (hf : Function.Injective ρ)
    [Finite V] : Nat.card C ≤ Nat.card V := by
  obtain ⟨v,hv⟩ := exists_cyclic_detecting_vector ρ
  apply Nat.card_le_card_of_injective (fun c => ρ c v)
  intro a b hab
  change ρ a v = ρ b v at hab
  have hfix : ρ (b⁻¹*a) v = v := by
    rw [map_mul,Module.End.mul_apply,hab]
    exact ρ.inv_self_apply b v
  have he : b⁻¹*a = 1 := hf ((hv _ hfix).trans (map_one ρ).symm)
  exact (inv_mul_eq_one.mp he).symm

/-- Too many cyclic actors force a nonidentity element acting trivially. -/
theorem exists_cyclic_kernel_of_card_lt (ρ : Representation K C V) [Finite V]
    (hlt : Nat.card V < Nat.card C) : ∃ c : C, c ≠ 1 ∧ ρ c = 1 := by
  by_contra! h
  have hf : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp (by
    apply bot_unique
    intro c hc
    by_cases he : c = 1
    · exact he
    · exact (h c he hc).elim)
  exact (Nat.not_lt_of_ge (cyclic_card_le ρ hf)) hlt

end Representation
