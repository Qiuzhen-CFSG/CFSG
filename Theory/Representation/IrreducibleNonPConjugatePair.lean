module

public import Mathlib.Algebra.Field.ZMod
public import Theory.GroupTheory.BaerSuzuki
public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Non-p conjugate pairs in faithful irreducible modular actions

Let a finite group act faithfully and irreducibly on a nonzero finite-dimensional
module over `ZMod p`, and let `a` have order `p`. If every conjugate of `a`
generated a `p`-group with `a`, the Baer–Suzuki p-core criterion would put `a`
in the p-core. That p-core is a normal p-subgroup, so modular fixed-point
theory and irreducibility put it in the representation kernel, contradicting
faithfulness. This supplies the pair-selection input for the quadratic
`SL₂` section argument, without restricting to odd primes.

The group-theoretic criterion is the Theory-level extraction of the
Alperin–Lyons proof of Gorenstein Chapter 3, Theorem 8.2. The modular fixed
point step uses the normal-invariants API and the p-group fixed-vector lemma
from `Theory.Representation.TwoDimensionalOddOrder`.
-/

namespace Representation

private theorem normal_p_subgroup_le_kernel
    {H V : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) H V) [IsIrreducible ρ]
    (N : Subgroup H) [N.Normal] (hN : IsPGroup p N) : N ≤ ρ.ker := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hchar : ringChar (ZMod p) ≠ 0 := by
    simpa [ZMod.ringChar_zmod_n] using (Fact.out : p.Prime).ne_zero
  have hp : IsPGroup (ringChar (ZMod p)) N := by
    simpa [ZMod.ringChar_zmod_n] using hN
  obtain ⟨vector, nonzero, fixed⟩ :=
    pGroup_fix_nonzero_vector hchar hp (ρ.comp N.subtype)
  apply le_ker_of_normal_invariants_ne_bot ρ N
  intro hbot
  have hmem : vector ∈ invariants (ρ.comp N.subtype) := fixed
  rw [hbot, Submodule.mem_bot] at hmem
  exact nonzero hmem

public theorem exists_non_p_conjugate_pair_of_faithful_irreducible
    {H V : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) H V) (faithful : Function.Injective ρ)
    [IsIrreducible ρ] (a : H) (order : orderOf a = p) :
    ∃ g : H, ¬ IsPGroup p (Subgroup.closure ({a, g * a * g⁻¹} : Set H)) := by
  classical
  by_contra hpair
  push Not at hpair
  have hcore : a ∈ pCore p H :=
    Subgroup.mem_pCore_of_conjugate_pairs_isPGroup a
      (IsPGroup.of_card (n := 1) (by simpa [Nat.card_zpowers, pow_one] using order))
      (by rintro g; exact hpair g)
  have hker := normal_p_subgroup_le_kernel ρ (pCore p H) pCore_isPGroup hcore
  have hone : a = 1 := faithful ((MonoidHom.mem_ker.mp hker).trans (map_one ρ).symm)
  have hpone : p = 1 := by simpa [hone] using order.symm
  exact (Fact.out : p.Prime).ne_one hpone

end Representation
