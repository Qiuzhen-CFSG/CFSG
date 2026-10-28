module
public import Theory.Character.MinimalDegree
public import Theory.Representation.PermutationBasisOrbits
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Permutation characters and transitive actions

The trace of the representation on the free complex vector space of a finite
set counts fixed points. Its invariant vectors are constant on each orbit, so
a transitive action has principal multiplicity one. Combining these facts with
the least nonprincipal degree identifies the remaining irreducible constituent.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Theory.Character

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]

omit [Finite G] in
/-- The character of the actual permutation representation counts fixed points. -/
public theorem permutation_character_eq_card_fixedBy (g : G) :
    (Representation.ofMulAction ℂ G X).character g =
      (Nat.card (MulAction.fixedBy X g) : ℂ) := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis X ℂ)]
  change (∑ x : X, LinearMap.toMatrix (MonoidAlgebra.basis X ℂ)
    (MonoidAlgebra.basis X ℂ) (Representation.ofMulAction ℂ G X g) x x) = _
  simp only [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    Representation.ofMulAction_single]
  simp [MonoidAlgebra.basis, Nat.card_eq_fintype_card, Fintype.card_subtype,
    MulAction.mem_fixedBy, Finsupp.single_apply, eq_comm]

/-- A transitive permutation representation has principal multiplicity one. -/
public theorem permutation_character_principal [Nonempty X] [MulAction.IsPretransitive G X] :
    scalarProduct G (Representation.ofMulAction ℂ G X).character 1 = 1 := by
  classical
  have : Subsingleton (MulAction.orbitRel.Quotient G X) :=
    (MulAction.pretransitive_iff_subsingleton_quotient G X).mp inferInstance
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  have hb (g : G) (x : X) :
      Representation.ofMulAction ℂ G X g (MonoidAlgebra.basis X ℂ x) =
        MonoidAlgebra.basis X ℂ (g • x) := by
    simp [MonoidAlgebra.basis_apply, Representation.ofMulAction_single]
  have h := Representation.permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card
    (Representation.ofMulAction ℂ G X) (MonoidAlgebra.basis X ℂ) hb
  have : Nonempty (MulAction.orbitRel.Quotient G X) :=
    ⟨Quotient.mk (MulAction.orbitRel G X) (Classical.arbitrary X)⟩
  have hc : Nat.card (MulAction.orbitRel.Quotient G X) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  calc
    scalarProduct G (Representation.ofMulAction ℂ G X).character 1 =
        (Module.finrank ℂ (Representation.ofMulAction ℂ G X).invariants : ℂ) := by
      simpa only [scalarProduct, Pi.one_apply, star_one, mul_one] using
        Representation.card_inv_mul_sum_char_eq_finrank (Representation.ofMulAction ℂ G X)
    _ = 1 := by rw [h, hc]; norm_num

/-- A transitive action of degree one greater than the least nonprincipal
irreducible degree has permutation character `1 + θ`, where `θ` is irreducible. -/
public theorem exists_irreducible_fixedBy_of_min_degree
    [Nonempty X] [MulAction.IsPretransitive G X]
    (d : ℕ) (hd : 0 < d) (hcard : Nat.card X = d + 1)
    (hmin : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ ≠ 1 →
      (d : ℝ) ≤ (θ 1).re) :
    ∃ θ : ClassFunction G, IsIrreducibleCharacter θ ∧ θ 1 = (d : ℂ) ∧
      ∀ g, (Nat.card (MulAction.fixedBy X g) : ℂ) = 1 + θ g := by
  have hdeg : (Representation.ofMulAction ℂ G X).character 1 = (d + 1 : ℕ) := by
    rw [permutation_character_eq_card_fixedBy]
    have hc : Fintype.card X = d + 1 := by simpa [Nat.card_eq_fintype_card] using hcard
    simp [MulAction.fixedBy_one_eq_univ, hc]
  obtain ⟨θ, hθ, hdθ, heq⟩ := eq_one_add_irreducible_of_min_degree
    (Representation.ofMulAction ℂ G X) d hd hdeg permutation_character_principal hmin
  exact ⟨θ, hθ, hdθ, fun g => (permutation_character_eq_card_fixedBy g).symm.trans (heq g)⟩

end Theory.Character
