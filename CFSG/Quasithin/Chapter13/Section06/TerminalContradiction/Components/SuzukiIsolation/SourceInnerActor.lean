module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceSemisimple
public import Theory.SpecificGroups.Suzuki.NormalizerInnerActors

/-!
# The original elementary actor on a marked Suzuki component

The component quotient representation is covariant under the actual H-action
on U_H/V₁. Prove this on representatives in A, then extend scalars. Applying
the kernel-preserving Suzuki inner lift to an elementary B≤H gives a single
matrix marking and root-valued homomorphism whose inner action is exactly the
operator covariance of the original extended representation.

The full actor B and its quotient-action kernel are retained. This supplies
the source input to the commuting multiplicity action on Suzuki isotypic
parts; it does not assume faithful action on an individual component.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), §13.6,
printed pp.934--935; the section U_H/V₁ is from Notation 13.5.8.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Section08 Ratio BenderSuzuki.MatrixGroups Representation
variable {G : Type*} [Group G] [Finite G]
  {V₁ V₃ H A : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))
local instance sourceInnerSpanCommGroup : CommGroup (Source.UH H V₃) := inferInstance

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- Ambient conjugation and the original component quotient action are covariant. -/
theorem componentQuotientRepresentation_covariance
    (h : H) (x : A ⧸ pCore 2 A) :
    representation H V₃ V₁ hn h * componentQuotientRepresentation hn hk hAH hHA x =
      componentQuotientRepresentation hn hk hAH hHA
        (normalizerPCoreQuotientAction A (inclusion hHA h) x) *
        representation H V₃ V₁ hn h := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
  change representation H V₃ V₁ hn h *
      componentQuotientRepresentation hn hk hAH hHA (QuotientGroup.mk' _ a) =
    componentQuotientRepresentation hn hk hAH hHA
      (quotientAut (pCore 2 A) (A.normalizerMonoidHom (inclusion hHA h))
        (QuotientGroup.mk' _ a)) * representation H V₃ V₁ hn h
  rw [quotientAut_apply_mk, componentQuotientRepresentation_mk,
    componentQuotientRepresentation_mk, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (h : G) * (a : G) = (h : G) * (a : G) * (h : G)⁻¹ * (h : G)
  group

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension preserves covariance of the literal two source actions. -/
theorem extendedComponentQuotientRepresentation_covariance
    (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (h : H) (x : A ⧸ pCore 2 A) :
    extendScalars (F := ZMod 2) (G := H) (V := Space H V₃ V₁) K (representation H V₃ V₁ hn) h *
      extendScalars (F := ZMod 2) (G := A ⧸ pCore 2 A) (V := Space H V₃ V₁) K (componentQuotientRepresentation hn hk hAH hHA) x =
    extendScalars (F := ZMod 2) (G := A ⧸ pCore 2 A) (V := Space H V₃ V₁) K (componentQuotientRepresentation hn hk hAH hHA)
      (normalizerPCoreQuotientAction A (inclusion hHA h) x) *
      extendScalars (F := ZMod 2) (G := H) (V := Space H V₃ V₁) K (representation H V₃ V₁ hn) h := by
  simp only [extendScalars_apply, ← LinearMap.baseChange_mul]
  rw [componentQuotientRepresentation_covariance hn hk hAH hHA]

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- The original elementary actor has a root homomorphism, exact kernel, and
operator covariance on the actual scalar-extended section U_H/V₁. -/
theorem source_elementary_root_actor
    (B : Subgroup G) (hBH : B ≤ H) (hB : ∀ b : B, b ^ 2 = 1)
    {m : ℕ} (hm : 1 ≤ m) (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] :
    ∃ (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A))
      (φ : B →* SuzukiRootSubgroup m),
      (∀ (b : B) (d : SuzukiMatrixGroup m),
        ((extendScalars (F := ZMod 2) (G := H) (V := Space H V₃ V₁) K (representation H V₃ V₁ hn)).comp (inclusion hBH)) b *
          markedExtendedComponentRepresentation hn hk hAH hHA K f d =
        markedExtendedComponentRepresentation hn hk hAH hHA K f
          ((φ b : SuzukiMatrixGroup m) * d * (φ b : SuzukiMatrixGroup m)⁻¹) *
          ((extendScalars (F := ZMod 2) (G := H) (V := Space H V₃ V₁) K (representation H V₃ V₁ hn)).comp (inclusion hBH)) b) ∧
      φ.ker = ((normalizerPCoreQuotientAction A).comp
        (inclusion (hBH.trans hHA))).ker ∧
      ∀ b, φ b ∈ center (SuzukiRootSubgroup m) := by
  obtain ⟨e', φ, hφ, hker, hc⟩ := suzuki_normalizer_quotient_root_coordinates
    A B (hBH.trans hHA) m hm e hB
  refine ⟨e'.symm, φ, ?_, hker, hc⟩
  intro b d
  have hmark : normalizerPCoreQuotientAction A (inclusion hHA (inclusion hBH b))
      (e'.symm d) = e'.symm ((φ b : SuzukiMatrixGroup m) * d *
        (φ b : SuzukiMatrixGroup m)⁻¹) := by
    apply e'.injective
    have hi : inclusion hHA (inclusion hBH b) = inclusion (hBH.trans hHA) b :=
      Subtype.ext rfl
    rw [hi, e'.apply_symm_apply]
    simpa only [MulEquiv.apply_symm_apply] using hφ b (e'.symm d)
  change extendScalars (F := ZMod 2) (G := H) (V := Space H V₃ V₁) K (representation H V₃ V₁ hn) (inclusion hBH b) *
      extendScalars (F := ZMod 2) (G := A ⧸ pCore 2 A) (V := Space H V₃ V₁) K (componentQuotientRepresentation hn hk hAH hHA) (e'.symm d) =
    extendScalars (F := ZMod 2) (G := A ⧸ pCore 2 A) (V := Space H V₃ V₁) K (componentQuotientRepresentation hn hk hAH hHA)
      (e'.symm ((φ b : SuzukiMatrixGroup m) * d * (φ b : SuzukiMatrixGroup m)⁻¹)) *
      extendScalars (F := ZMod 2) (G := H) (V := Space H V₃ V₁) K (representation H V₃ V₁ hn) (inclusion hBH b)
  rw [extendedComponentQuotientRepresentation_covariance hn hk hAH hHA, hmark]

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
