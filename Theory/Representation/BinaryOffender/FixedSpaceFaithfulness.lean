module

public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.RatioInheritance
public import Theory.GroupAction.ThompsonAB

/-!
# Faithful restriction to fixed spaces of two-groups

Thompson A×B bounds the kernel on a two-group's fixed space by the
odd actor's two-core. That core is trivial for an odd prime group.
Transporting the given binary representation to its additive group proves
faithfulness on the literal fixed subspace and injectivity of its map to
the actual action image. Commuting actors also preserve that fixed space.

Source: Aschbacher--Smith, A.1.18, as used in D.2.13, printed p.185.
The source application is FittingOffenders/HyperplaneReduction.lean.
-/

public section
open Subgroup
open Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Commuting actors preserve the fixed space of one another. -/
theorem le_stabilizer_fixedSpace_of_commutator_eq_bot
    (P B : Subgroup G) (hPB : ⁅P,B⁆ = ⊥) :
    P ≤ subspaceStabilizer ρ (fixedSpace ρ B) := by
  apply le_subspaceStabilizer
  intro p hp v hv b
  have hc : (b : G) * p = p * b :=
    (commutator_eq_bot_iff_le_centralizer.mp hPB hp) b b.property
  change ∀ b : B, ρ b v = v at hv
  change ρ b (ρ p v) = ρ p v
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hv b]

/-- Thompson A×B on the original binary representation: an odd prime group
commuting with a two-group remains faithful on the latter's fixed space. -/
theorem fixedSpace_primeGroup_kernel_eq_bot
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P B : Subgroup G) (hP : IsPGroup p P) (hB : IsPGroup 2 B)
    (hPB : ⁅P,B⁆ = ⊥) :
    subspaceKernel ρ (fixedSpace ρ B) P = ⊥ := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ hf
  have hcore : pCore 2 P = ⊥ := by
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 p
      (fun he => (by decide : ¬ Odd (2 : ℕ)) (he.symm ▸ hp)) _ _ pCore_isPGroup (hP.to_subgroup _))
  have hbound := thompson_fixedPoints_kernel_le_pCore (G := Multiplicative V) P B
    (IsElementaryAbelian.isPGroup 2 (Multiplicative V)) hB hPB
  apply bot_unique
  intro g hg
  have hmem : (⟨g, hg.1⟩ : P) ∈ fixingSubgroup P
      (FixedPoints.subgroup B (Multiplicative V) : Set (Multiplicative V)) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact congrArg Multiplicative.ofAdd (hg.2 v.toAdd hv)
  have hz := hbound hmem
  rw [hcore, mem_bot] at hz
  exact congrArg Subtype.val hz

/-- The literal map to the faithful action image is injective on the odd
prime group; no abstract replacement of the representation is involved. -/
theorem fixedSpace_primeGroup_action_injective
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P B : Subgroup G) (hP : IsPGroup p P) (hB : IsPGroup 2 B)
    (hPB : ⁅P,B⁆ = ⊥) :
    Function.Injective (subgroupActionHom ρ (fixedSpace ρ B) P
      (le_stabilizer_fixedSpace_of_commutator_eq_bot ρ P B hPB)) := by
  apply (subgroupActionHom_injective_iff ρ (fixedSpace ρ B) P _).mpr
  exact fixedSpace_primeGroup_kernel_eq_bot ρ hf hp P B hP hB hPB
end Representation.BinaryOffender

