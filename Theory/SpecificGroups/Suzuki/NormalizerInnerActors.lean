module
public import Theory.SpecificGroups.Suzuki.ElementaryInnerActors
public import Theory.GroupTheory.NormalizerQuotientOuterPair

/-!
# Literal root coordinates for a normalizing elementary actor

Apply the homomorphic Suzuki inner lift to the original conjugation action of
A ≤ N_H(D), retaining A itself. The root-valued homomorphism has kernel exactly
C_A(D). The same construction on the literal quotient D/O₂(D) retains the
kernel of that quotient action; it does not replace this kernel by C_A(D).

The model equivalence is changed by one inner conjugation to place the actor
in the standard Suzuki root group. These interfaces supply the full actor
and its kernel for the multiplicity-space action in Aschbacher--Smith,
13.6.26, printed pp.934--935.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- The original normalizing actor has central-root coordinates and kernel C_A(D). -/
theorem suzuki_normalizer_root_coordinates
    {H : Type*} [Group H] (D A : Subgroup H)
    (hAD : A ≤ normalizer (D : Set H))
    (m : ℕ) (hm : 1 ≤ m) (e : D ≃* SuzukiMatrixGroup m)
    (hA : ∀ a : A, a ^ 2 = 1) :
    ∃ (e' : D ≃* SuzukiMatrixGroup m) (φ : A →* SuzukiRootSubgroup m),
      (∀ (a : A) (z : D), e' (D.normalizerMonoidHom (inclusion hAD a) z) =
        (φ a : SuzukiMatrixGroup m) * e' z * (φ a : SuzukiMatrixGroup m)⁻¹) ∧
      φ.ker = (centralizer (D : Set H)).subgroupOf A ∧
      ∀ a, φ a ∈ center (SuzukiRootSubgroup m) := by
  obtain ⟨e', φ, hφ, hk, hc⟩ := suzuki_root_coordinates m hm e
    (D.normalizerMonoidHom.comp (inclusion hAD)) hA
  refine ⟨e', φ, hφ, hk.trans ?_, hc⟩
  ext a
  change D.normalizerMonoidHom (inclusion hAD a) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- The literal action on D/O₂(D) has central-root coordinates with its original kernel. -/
theorem suzuki_normalizer_quotient_root_coordinates
    {H : Type*} [Group H] (D A : Subgroup H)
    (hAD : A ≤ normalizer (D : Set H))
    (m : ℕ) (hm : 1 ≤ m) (e : D ⧸ pCore 2 D ≃* SuzukiMatrixGroup m)
    (hA : ∀ a : A, a ^ 2 = 1) :
    ∃ (e' : D ⧸ pCore 2 D ≃* SuzukiMatrixGroup m)
      (φ : A →* SuzukiRootSubgroup m),
      (∀ (a : A) (z : D ⧸ pCore 2 D),
        e' (normalizerPCoreQuotientAction D (inclusion hAD a) z) =
          (φ a : SuzukiMatrixGroup m) * e' z * (φ a : SuzukiMatrixGroup m)⁻¹) ∧
      φ.ker = ((normalizerPCoreQuotientAction D).comp (inclusion hAD)).ker ∧
      ∀ a, φ a ∈ center (SuzukiRootSubgroup m) := by
  exact suzuki_root_coordinates m hm e
    ((normalizerPCoreQuotientAction D).comp (inclusion hAD)) hA

end BenderSuzuki.MatrixGroups
