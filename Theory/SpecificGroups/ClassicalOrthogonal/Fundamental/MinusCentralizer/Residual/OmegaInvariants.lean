module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Scalars
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Determinant
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.RankOne
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor

/-!
# Commutator invariants of the minus complement

Elementary transformations generate the literal complementary commutator
for every `r ≥ 1` over every finite odd field, including F₃. The rank-one
proof uses the actual minus-four/Hermitian comparison; higher ranks use
two hyperbolic pairs. Consequently the entire projective block image lies
in the marked prime-to-characteristic residual.

The imported determinant and intrinsic spinor comparisons prove that identity
extension reflects commutator membership. Their value on negation, together
with the already proved finite-field discriminant arithmetic, shows that
the common negative scalar occurs exactly when `r + 1` is odd and the field
cardinality is three modulo four. We specialize the literal projective block
kernel: it is then cyclic of order two, and otherwise trivial.

These results discharge the elementary-generation and commutator-restriction
premises of the residual assembly. The full-centralizer decomposition and
final residual equality belong to that separate assembly.

Source: Aschbacher–Smith A.2.17, printed p.39; GLS3 §2.7, printed pp.88–89.
This extension deliberately does not import the residual assembly module.
-/

@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
variable {F : Type*} [Field F] [Finite F]

/-- Elementary transformations generate the actual complementary commutator
in every source rank, including the four-dimensional complement over F₃.
This is the `hgen` premise of `projectiveBlockHom_range_eq_residual_of_structure`. -/
theorem complement_elementary_eq_omega (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (Minus.quadraticForm F (r + 1)) =
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) := by
  by_cases h : r = 1
  · subst r
    exact complement_elementary_eq_omega_rankOne h2
  · exact complement_elementary_eq_omega_of_two_le r (by omega) h2

/-- The entire actual block image lies in the marked residual, including at
Witt index one. Both factors map into the literal residual of the centralizer. -/
theorem projectiveBlockHom_range_le_residual
    (p : ℕ) [CharP F p] (r : ℕ) (hr : 1 ≤ r) (hq : 2 < Nat.card F)
    (h2 : (2 : F) ≠ 0) :
    (projectiveBlockHom r hq).range ≤ centralizerResidualImage p r hq := by
  let f := blockToCentralizer (F := F) r hq
  let e := MulEquiv.subgroupCongr (complement_elementary_eq_omega r hr h2)
  rintro _ ⟨g, rfl⟩
  have h1 := Matrix.SL2.map_mem_primeToResidual p (f.comp (MonoidHom.inl _ _)) g.1
  have h2 := SplitOddBlocks.elementary_map_mem_primeToResidual p
    (Minus.quadraticForm F (r + 1))
    ((f.comp (MonoidHom.inr _ _)).comp e.toMonoidHom) (e.symm g.2)
  have hg : f g ∈ centralizerResidual p r hq := by
    have he : g = (g.1, 1) * (1, g.2) := by simp
    rw [he, map_mul]
    apply Subgroup.mul_mem _ h1
    change f (1, e (e.symm g.2)) ∈ _ at h2
    simpa only [MulEquiv.apply_symm_apply] using h2
  exact ⟨f g, hg, rfl⟩

/-- The retained higher-rank specialization of residual containment. -/
theorem projectiveBlockHom_range_le_residual_of_two_le
    (p : ℕ) [CharP F p] (r : ℕ) (hr : 2 ≤ r) (hq : 2 < Nat.card F)
    (h2 : (2 : F) ≠ 0) :
    (projectiveBlockHom r hq).range ≤ centralizerResidualImage p r hq :=
  projectiveBlockHom_range_le_residual p r (by omega) hq h2

/-- The unconditional parity and field-cardinality criterion for negation in
the full complementary commutator. -/
theorem negativeComplement_mem_omega_iff
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0) :
    negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      Odd (r + 1) ∧ Nat.card F % 4 = 3 :=
  negativeComplement_mem_iff_of_squareCriterion r h2
    (negativeComplement_mem_omega_iff_isSquare r hr h2)

/-- In precisely the scalar case, simultaneous negation generates the actual
projective block kernel. Its complementary membership is proved here. -/
theorem projectiveBlockHom_kernel_eq_zpowers_of_parity
    (r : ℕ) (hr : 1 ≤ r) (hq : 2 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (hc : Odd (r + 1) ∧ Nat.card F % 4 = 3) :
    (projectiveBlockHom r hq).ker = Subgroup.zpowers
      (commonNegative r ((negativeComplement_mem_omega_iff r hr h2).mpr hc)) :=
  projectiveBlockHom_kernel_eq_zpowers r hq _

/-- The projective block map is injective exactly outside the common negative
scalar case; no commutator-membership premise remains. -/
theorem projectiveBlockHom_injective_iff_parity
    (r : ℕ) (hr : 1 ≤ r) (hq : 2 < Nat.card F) (h2 : (2 : F) ≠ 0) :
    Function.Injective (projectiveBlockHom r hq) ↔
      ¬ (Odd (r + 1) ∧ Nat.card F % 4 = 3) :=
  projectiveBlockHom_injective_iff_of_scalarCriterion r hq h2
    (negativeComplement_mem_omega_iff r hr h2)

/-- The exact order of the common-scalar kernel in all source ranks. -/
theorem projectiveBlockHom_kernel_card
    (r : ℕ) (hr : 1 ≤ r) (hq : 2 < Nat.card F) (h2 : (2 : F) ≠ 0) :
    Nat.card (projectiveBlockHom r hq).ker =
      if Odd (r + 1) ∧ Nat.card F % 4 = 3 then 2 else 1 :=
  projectiveBlockHom_kernel_card_of_scalarCriterion r hq h2
    (negativeComplement_mem_omega_iff r hr h2)

end ClassicalOrthogonal.Fundamental.MinusCentralizer
