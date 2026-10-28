module
public import Theory.Representation.SL2.MinimalBinaryDegree
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging

/-!
# Two minimum-degree factors under an odd fixed-free actor

A binary SL₂(2ⁿ)-module of dimension at most 4n, with no fixed vector
for an odd subgroup, has two irreducible factors of dimension 2n whenever
it has a proper nonzero invariant subspace. Odd-order averaging makes
fixed vectors lift through that quotient. The binary minimum-degree
bound then forces equality for both dimensions, and the minimum-degree
irreducibility criterion finishes the assertion.

This is the constituent-order step in DGS, Groups and Graphs (1985),
proof of (12.9), printed p.189. The literal C/W application is in
CommutingThreeProfile/SuzukiCentralizerFactors.
-/

public noncomputable section
open Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem degree_ge_of_no_invariants
    (ρ : Representation (ZMod 2) SL(2,F) V) [Nontrivial V]
    (hf : ρ.invariants = ⊥) {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2^n) :
    2*n ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨U,hU,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  let : U.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom U).mpr hU
  have hnt : ∃ g, U.toRepresentation g ≠ 1 := by
    by_contra! hh
    apply hU.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hf.le
    intro g
    exact congrArg Subtype.val (congrArg
      (fun f : Module.End (ZMod 2) U.toSubmodule => f ⟨v,hv⟩) (hh g))
  exact (Unsigned.irreducible_finrank_bound 2 U.toRepresentation hnt n hn hF).trans
    (Submodule.finrank_le U.toSubmodule)

/-- Every proper nonzero invariant section in a module of degree at most four
field degrees splits the degree into two irreducible minimum-degree factors. -/
theorem small_factors_of_odd_fixed_free
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (D : Subgroup SL(2,F)) (ho : Odd (Nat.card D))
    (hf : fixedSpace ρ D = ⊥)
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2^n)
    (hd : Module.finrank (ZMod 2) V ≤ 4*n)
    (U : Subrepresentation ρ) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    Module.finrank (ZMod 2) U.toSubmodule = 2*n ∧
    Module.finrank (ZMod 2) (V ⧸ U.toSubmodule) = 2*n ∧
    U.toRepresentation.IsIrreducible ∧ U.quotientRepresentation.IsIrreducible := by
  have hUb : U.toSubmodule ≠ ⊥ := fun he => hU (Subrepresentation.toSubmodule_injective he)
  have hUtop : U.toSubmodule ≠ ⊤ := fun he => hUt (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hUb
  let : Nontrivial (V ⧸ U.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hUtop
  have hfU : U.toRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    apply hf.le
    intro d
    exact congrArg Subtype.val (hv (d : SL(2,F)))
  have hfQ : fixedSpace U.quotientRepresentation D = ⊥ := by
    rw [←fixedSpace_map_eq_of_odd ρ U.quotientRepresentation U.toSubmodule.mkQ
      (fun _ _ => rfl) U.toSubmodule.mkQ_surjective D ho,hf,Submodule.map_bot]
  have hfQ' : U.quotientRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply hfQ.le
    intro d
    exact hv d
  have hdu := degree_ge_of_no_invariants U.toRepresentation hfU hn hF
  have hdq := degree_ge_of_no_invariants U.quotientRepresentation hfQ' hn hF
  have hsum := Submodule.finrank_quotient_add_finrank U.toSubmodule
  have hu : Module.finrank (ZMod 2) U.toSubmodule = 2*n := by omega
  have hq : Module.finrank (ZMod 2) (V ⧸ U.toSubmodule) = 2*n := by omega
  exact ⟨hu,hq,
    irreducible_of_fixed_free_minimal_binary_degree U.toRepresentation hfU hn hF hu.le,
    irreducible_of_fixed_free_minimal_binary_degree U.quotientRepresentation hfQ' hn hF hq.le⟩
end Representation.SL2
