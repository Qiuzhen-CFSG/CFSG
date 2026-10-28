module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.SymplecticGroup
public import BenderSuzuki.MatrixGroups.Unitary

/-!
# Isomorphism predicates for concrete classical groups

These predicates specify projective matrix groups over finite fields of a given
order. For unitary groups, `q` is the order of the fixed field: the matrices are
over a field of order `q²`, and conjugation is explicitly `x ↦ x^q`. Allowing an
arbitrary nondegenerate Hermitian form makes the interface usable for the
existing antidiagonal models as well as diagonal models.

Transport is composition of multiplicative equivalences; no recognition from
order or classification hypothesis occurs here. The unitary convention agrees
with Aschbacher–Smith, *The Classification of Quasithin Groups*, §A.2, footnote 3
(printed p.38). The carriers are the existing projective matrix constructions.
-/

@[expose] public section

universe u v

namespace ClassicalGroup

/-- The projective symplectic group in dimension `2r`, as the central quotient
of the group preserving the standard alternating form. -/
abbrev PSp (r : ℕ) (F : Type*) [Field F] :=
  (Matrix.symplecticGroup (Fin r) F) ⧸
    Subgroup.center (Matrix.symplecticGroup (Fin r) F)

/-- Isomorphism with the actual `PSL_n(q)` matrix group. -/
def IsPSL (G : Type u) [Group G] (n q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) F)

/-- Isomorphism with `PSU_n(q)`, with matrices over a field of order `q²`. -/
def IsPSU (G : Type u) [Group G] (n q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (J : BenderSuzuki.MatrixGroups.HermitianForm n F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
      Nonempty (G ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)

/-- Isomorphism with the actual `PSp_{2r}(q)` matrix group. -/
def IsPSp (G : Type u) [Group G] (r q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* PSp r F)

variable {G : Type u} {H : Type v} [Group G] [Group H] {n q : ℕ}

/-- Transport a linear model across an isomorphism. -/
theorem IsPSL.of_mulEquiv (h : IsPSL G n q) (e : H ≃* G) : IsPSL H n q := by
  rcases h with ⟨F, hF, hfin, hq, ⟨f⟩⟩
  exact ⟨F, hF, hfin, hq, ⟨e.trans f⟩⟩

/-- Transport a unitary model while keeping its field and Hermitian form. -/
theorem IsPSU.of_mulEquiv (h : IsPSU G n q) (e : H ≃* G) : IsPSU H n q := by
  rcases h with ⟨F, hF, hfin, J, hq, hconj, ⟨f⟩⟩
  exact ⟨F, hF, hfin, J, hq, hconj, ⟨e.trans f⟩⟩

/-- Transport a symplectic model across an isomorphism. -/
theorem IsPSp.of_mulEquiv (h : IsPSp G n q) (e : H ≃* G) : IsPSp H n q := by
  rcases h with ⟨F, hF, hfin, hq, ⟨f⟩⟩
  exact ⟨F, hF, hfin, hq, ⟨e.trans f⟩⟩

theorem isPSL_mulEquiv_iff (e : G ≃* H) : IsPSL G n q ↔ IsPSL H n q :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isPSU_mulEquiv_iff (e : G ≃* H) : IsPSU G n q ↔ IsPSU H n q :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isPSp_mulEquiv_iff (e : G ≃* H) : IsPSp G n q ↔ IsPSp H n q :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end ClassicalGroup
