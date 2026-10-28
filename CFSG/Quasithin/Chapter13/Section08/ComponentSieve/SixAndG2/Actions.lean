module

public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# From module commutators to subgroup ranks

The two rank-three contributions in Aschbacher–Smith 13.8.27 (printed
p.963) concern actual subgroup sections. An equivariant linear coordinate
map for conjugation identifies a displacement with the group commutator.
The linear span of these displacements therefore lies in the coordinate
subspace of any subgroup containing the group commutators. Counting that
subspace gives the rank bound.

Normality is relative to the chosen acting overgroup. Applying this also
inside `H/U_H` handles the contribution from `V_H/U_H`; a separate vector
space with no conjugation compatibility would not give the asserted bound.
-/

public section

open Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
variable {J W : Type*} [Group J] [Finite J]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A compatible conjugation representation transfers a module displacement
bound to the containing elementary abelian subgroup. -/
theorem commutator_dimension_le_rank
    (U D A : Subgroup J) [U.Normal] [IsElementaryAbelian 2 U]
    (ρ : Representation (ZMod 2) J W) (E : Additive U ≃ₗ[ZMod 2] W)
    (he : ∀ a : J, ∀ u : U, ρ a (E (Additive.ofMul u)) =
      E (Additive.ofMul ⟨a * u.val * a⁻¹,
        (inferInstance : U.Normal).conj_mem u.val u.property a⟩))
    (hDU : D ≤ U) (hcomm : ⁅A, U⁆ ≤ D) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ rank D := by
  let S : Submodule (ZMod 2) (Additive U) :=
    (AddSubgroup.toZModSubmodule (n := 2)) (D.subgroupOf U).toAddSubgroup
  have hS : Nat.card S = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDU).toEquiv
  have hd : Module.finrank (ZMod 2) S = rank D := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
    rw [hS, Nat.card_zmod] at hc
    have hl := congrArg (Nat.log 2) hc
    rw [Nat.log_pow Nat.one_lt_two] at hl
    exact hl.symm
  have hle : subspaceCommutator ρ ⊤ A ≤ S.map E.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, w, _, rfl⟩
    obtain ⟨u, rfl⟩ := E.surjective w
    let ua : U := ⟨a * u.toMul.val * a⁻¹,
      (inferInstance : U.Normal).conj_mem u.toMul.val u.toMul.property a⟩
    refine ⟨Additive.ofMul ua - u, ?_, ?_⟩
    · change (a * u.toMul.val * a⁻¹) / u.toMul.val ∈ D
      simpa only [div_eq_mul_inv, commutatorElement_def] using
        hcomm (Subgroup.commutator_mem_commutator ha u.toMul.property)
    · rw [map_sub]
      exact congrArg (fun x => x - E u) (he a u.toMul).symm
  have hdmap := E.finrank_map_eq S
  have hdim := Submodule.finrank_mono hle
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
