module

public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Derived subgroups of symplectic Sylow normalizers

Both determinant characters kill commutators. Their common kernel in the
flag Borel is the unipotent subgroup, so [B,B] lies in U. The equality
B = N(U) and Sylow conjugacy give [N(S),N(S)] ≤ S for every Sylow
two-subgroup over a field of two-power order. An actual multiplicative
equivalence transports this inclusion to another carrier.

This is the inner-kernel calculation needed in Aschbacher--Smith,
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
It does not assert that an arbitrary odd subgroup normalizes S.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

/-- Determinants kill the commutators of a subspace stabilizer. -/
theorem commutator_stabilizer_le_determinantKernel (W : Submodule F (Vector F)) :
    ⁅stabilizer W, stabilizer W⁆ ≤ determinantKernel W := by
  apply commutator_le.mpr
  intro a ha b hb
  let x : stabilizer W := ⟨a, ha⟩
  let y : stabilizer W := ⟨b, hb⟩
  refine ⟨⁅x, y⁆, ?_, rfl⟩
  change determinantCharacter W ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- Both flag characters kill the derived subgroup of the Borel. -/
theorem commutator_borel_le_unipotent :
    ⁅borel (F := F), borel (F := F)⁆ ≤ unipotent (F := F) := by
  exact le_inf
    ((commutator_mono (show borel (F := F) ≤ stabilizer (point F) from inf_le_left)
      (show borel (F := F) ≤ stabilizer (point F) from inf_le_left)).trans
      (commutator_stabilizer_le_determinantKernel (point F)))
    ((commutator_mono (show borel (F := F) ≤ stabilizer (plane F) from inf_le_right)
      (show borel (F := F) ≤ stabilizer (plane F) from inf_le_right)).trans
      (commutator_stabilizer_le_determinantKernel (plane F)))

variable [Finite F]
/-- A Sylow two-normalizer has abelian quotient by its Sylow subgroup. -/
theorem commutator_sylow_normalizer_le {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    ⁅normalizer (S : Set (Sp F)), normalizer (S : Set (Sp F))⁆ ≤ (S : Subgroup (Sp F)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn)
  let a := MulAut.conj g
  have hS : (S : Subgroup (Sp F)).map a.toMonoidHom = unipotent :=
    congrArg (fun V : Sylow 2 (Sp F) => (V : Subgroup (Sp F))) hg
  have hN : (normalizer (S : Set (Sp F))).map a.toMonoidHom ≤ borel := by
    rw [borel_eq_normalizer_unipotent, ← hS]
    exact fun _ hx => (S : Subgroup (Sp F)).le_normalizer_map a.toMonoidHom hx
  have hc : (⁅normalizer (S : Set (Sp F)), normalizer (S : Set (Sp F))⁆).map
      a.toMonoidHom ≤ (S : Subgroup (Sp F)).map a.toMonoidHom := by
    rw [map_commutator, hS]
    exact (commutator_mono hN hN).trans commutator_borel_le_unipotent
  exact (map_le_map_iff_of_injective a.injective).mp hc

/-- Transport the normalizer commutator bound through the actual matrix isomorphism. -/
theorem commutator_sylow_normalizer_le_of_equiv {Q : Type*} [Group Q] [Finite Q]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n) (e : Q ≃* Sp F)
    (S : Sylow 2 Q) :
    ⁅normalizer (S : Set Q), normalizer (S : Set Q)⁆ ≤ (S : Subgroup Q) := by
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hN : (normalizer (S : Set Q)).map e.toMonoidHom ≤ normalizer (U : Set (Sp F)) :=
    fun _ hx => (S : Subgroup Q).le_normalizer_map e.toMonoidHom hx
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [map_commutator]
  exact (commutator_mono hN hN).trans (commutator_sylow_normalizer_le hF hn U)

end Theory.SpecificGroups.SymplecticFour
