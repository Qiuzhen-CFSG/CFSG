module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Residual
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Index

/-!
# The half-Frobenius fixed group and its two-residual in Sp₄

For |F| = 2^(2m), m ≥ 1, `representative m` is the actual entrywise
m-th Frobenius and has order two. Its fixed coefficient field `halfField m`
has order 2^m (`card_halfField`). The constructed `fixedEquiv` identifies
its fixed group with Sp₄ over that field, and `residualEquiv` identifies the
two-residual with the derived subgroup of that same matrix group. Their
inclusion equations and `embedded_residual_eq` retain the ambient embedding.
At m = 1 the residual is explicitly A₆, through the binary polar representation.
For every ambient Sylow two-subgroup the fixed intersection has index at least
(2^m)^4 (`fixed_index_lower_bound`), hence greater than two (`two_lt_fixed_index`).

The square identity follows from x^|F| = x; the index bound excludes the
identity automorphism. Descent, the binary/nonbinary residual calculation,
and the Sylow order comparison are proved in the imported extension modules.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.1.4(4) and the field case of Lemma 16.1.8,
printed pp.1171–1173. This treats the explicit field representative; no
classification or conjugacy of arbitrary automorphisms is assumed.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open Subgroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The representative squares to the identity by the finite-field power identity. -/
theorem representative_sq {m : ℕ} (hF : Nat.card F = 2 ^ (2 * m)) :
    representative (F := F) m ^ 2 = 1 := by
  let _ := Fintype.ofFinite F
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  ext i j
  change ((frobeniusEquiv F 2)^m) (((frobeniusEquiv F 2)^m) (g.val i j)) = g.val i j
  rw [← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def,
    iterateFrobeniusEquiv_def, ← pow_mul, ← pow_add, ← two_mul, ← hF]
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card (g.val i j)

/-- The prescribed representative is an involution, rather than the identity. -/
theorem representative_orderOf {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m)) : orderOf (representative (F := F) m) = 2 := by
  apply orderOf_eq_prime (representative_sq hF)
  intro hr
  have hfix : (representative (F := F) m).fixedSubgroup = ⊤ := by
    ext x
    simp [MulAut.mem_fixedSubgroup, hr]
  have h := two_lt_fixed_index hm hF (unipotentSylow hF (by omega))
  rw [hfix] at h
  rw [top_subgroupOf, index_top] at h
  omega

/-- The derived binary fixed-field endpoint is the actual A₆ carrier. -/
def binaryFixedResidualEquivAlternatingSix (hF : Nat.card F = 4) :
    pResidual 2 (representative (F := F) 1).fixedSubgroup ≃* alternatingGroup (Fin 6) :=
  (residualEquiv ((frobeniusEquiv F 2)^1)).trans
    (Binary.derivedEquivAlternatingSix (by
      change Nat.card (halfField (F := F) 1) = 2
      exact card_halfField (F := F) (m := 1) (by omega) (by simpa using hF)))

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
