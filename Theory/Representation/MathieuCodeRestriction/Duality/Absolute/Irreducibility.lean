module

public import Theory.Representation.MathieuCodeRestriction
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.SubrepresentationLattice

/-!
# Irreducibility of the eleven-dimensional Mathieu modules

Every nonzero subrepresentation is faithful: simplicity makes its kernel
trivial or the whole group, and the latter would give a global fixed vector.
The order of 2 modulo 23 is eleven, so a faithful binary subrepresentation
already has the full dimension.

For the native M₂₃ restriction, conjugate the certified 23-cycle fixing
point one into the stabilizer of point zero. The exact image theorem for
`pointEmbedding` then transfers the vanishing norm to this restriction,
proving that its global fixed space is zero.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.13.1–2,
printed p.395. The actions are the actual Golay quotient and even-core
quotient, with no irreducibility or model-identification premise.
-/

public section

open Representation Sporadic.Mathieu
open scoped BigOperators
namespace MathieuCode

private theorem irreducible_of_simple_of_degree
    {G V : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hz : ρ.invariants = ⊥)
    (hd : Module.finrank (ZMod 2) V = 11) (h23 : 23 ∣ Nat.card G) :
    ρ.IsIrreducible := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hd]; decide : 0 < Module.finrank (ZMod 2) V)
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hf : Function.Injective N.toRepresentation := by
    rcases N.toRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact N.toRepresentation.ker_eq_bot_iff.mp hk
    · have he : N.toRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have hle : N.toSubmodule ≤ ρ.invariants := by
        intro v hv g
        have h := DFunLike.congr_fun (congrArg (fun σ => σ g) he) ⟨v, hv⟩
        exact congrArg Subtype.val h
      rw [hz] at hle
      exact (hN (Subrepresentation.toSubmodule_injective (le_bot_iff.mp hle))).elim
  have hlo := BinaryPrimeDegree.orderOf_le_finrank N.toRepresentation hf
    (by decide : Nat.Prime 23) (by decide : 23 ≠ 2) h23
  rw [BinaryPrimeDegree.orderOf_two_mod_twentyThree] at hlo
  apply Subrepresentation.toSubmodule_injective
  by_contra hnt
  have hlt := Submodule.finrank_lt hnt
  rw [hd] at hlt
  omega

private theorem restriction_invariants_eq_bot_of_cycle_norm
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V)
    (hn : ∀ v, (∑ k : Fin 23, ρ (cycle23 ^ k.val) v) = 0) :
    Representation.invariants (ρ.comp pointEmbedding) = ⊥ := by
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq M24 (0 : Fin 24) 1
  have hc : cycle23 ∈ MulAction.stabilizer M24 (1 : Fin 24) := by
    change (m24GeneratorA * m24GeneratorB) (1 : Fin 24) = 1
    decide +kernel
  have hc' (k : ℕ) : (cycle23 ^ k) • (1 : Fin 24) = 1 :=
    (MulAction.stabilizer M24 (1 : Fin 24)).pow_mem hc k
  apply le_antisymm _ bot_le
  intro v hv
  have hw (k : Fin 23) : ρ (cycle23 ^ k.val) (ρ t v) = ρ t v := by
    have hm : t⁻¹ * cycle23 ^ k.val * t ∈ pointEmbedding.range := by
      rw [pointEmbedding_range]
      change (t⁻¹ * cycle23 ^ k.val * t) • (0 : Fin 24) = 0
      simp only [mul_smul, ht, hc']
      exact inv_smul_eq_iff.mpr ht.symm
    obtain ⟨g, hg⟩ := hm
    have hh := congrArg (ρ t) (hv g)
    change ρ t (ρ (pointEmbedding g) v) = ρ t v at hh
    rw [hg] at hh
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using hh
  have hs := hn (ρ t v)
  simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hs
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)] at hs
  have h23 : (23 : ZMod 2) = 1 := by decide
  change (23 : ZMod 2) • ρ t v = 0 at hs
  rw [h23, one_smul] at hs
  have hs' := congrArg (ρ t⁻¹) hs
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, map_zero, Submodule.mem_bot] using hs'


/-- The native point-stabilizer action has no nonzero invariant code vector. -/
theorem m23Code_invariants_eq_bot : m23CodeRepresentation.invariants = ⊥ :=
  restriction_invariants_eq_bot_of_cycle_norm codeRepresentation code_sum_cycle

/-- The native point-stabilizer action has no nonzero invariant cocode vector. -/
theorem m23Cocode_invariants_eq_bot : m23CocodeRepresentation.invariants = ⊥ :=
  restriction_invariants_eq_bot_of_cycle_norm cocodeRepresentation cocode_sum_cycle

/-- The eleven-dimensional code action of M₂₄ is irreducible. -/
theorem code_isIrreducible : codeRepresentation.IsIrreducible := by
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  exact irreducible_of_simple_of_degree codeRepresentation code_invariants_eq_bot
    finrank_code (by rw [m24_order]; norm_num)

/-- The eleven-dimensional cocode action of M₂₄ is irreducible. -/
theorem cocode_isIrreducible : cocodeRepresentation.IsIrreducible := by
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  exact irreducible_of_simple_of_degree cocodeRepresentation cocode_invariants_eq_bot
    finrank_cocode (by rw [m24_order]; norm_num)

/-- The actual restriction of the code action to M₂₃ is irreducible. -/
theorem m23Code_isIrreducible : m23CodeRepresentation.IsIrreducible := by
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  exact irreducible_of_simple_of_degree m23CodeRepresentation m23Code_invariants_eq_bot
    finrank_code (by rw [m23_order]; norm_num)

/-- The actual restriction of the cocode action to M₂₃ is irreducible. -/
theorem m23Cocode_isIrreducible : m23CocodeRepresentation.IsIrreducible := by
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  exact irreducible_of_simple_of_degree m23CocodeRepresentation m23Cocode_invariants_eq_bot
    finrank_cocode (by rw [m23_order]; norm_num)

/-- Faithfulness is retained along the injective native M₂₃ embedding. -/
theorem m23Code_faithful : Function.Injective m23CodeRepresentation :=
  code_faithful.comp pointEmbedding_injective

/-- Faithfulness is retained along the injective native M₂₃ embedding. -/
theorem m23Cocode_faithful : Function.Injective m23CocodeRepresentation :=
  cocode_faithful.comp pointEmbedding_injective

end MathieuCode
