module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourceStarComponent
public import Theory.Representation.Suzuki.AmbientSteinbergCoordinates
/-!
# The original quotient actor fixes the Suzuki Steinberg part

Apply the full ambient multiplicity-coordinate theorem to the actual elementary
actor B≤H/O₂(H) and the literal component image A*. The canonical identification
A/O₂(A)≃A* then rewrites the result in the source marked component action on
K⊗(U_H/V₁). No lift of B to an elementary subgroup of H is assumed.

The remaining independent source inputs are quadraticity and the original
ratio displacement bound, together with the bound on B∩C(A*). The latter
is supplied by the exceptional component automorphism calculation. The full
actor B, rather than its image on a selected summand, occurs in every bound.

Source: Aschbacher–Smith §13.6, printed pp.934–935, with Notation13.5.8.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative TensorProduct MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Section08 Ratio BenderSuzuki.MatrixGroups Representation Module
open Representation.BinaryOffender.NaturalTensor
variable {G : Type*} [Group G] [Finite G]
  {V₁ V₃ H A : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))
local instance sourceCoordinatesCommGroup : CommGroup (Source.UH H V₃) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The actual small-ratio actor fixes the canonical full Steinberg part of
the original scalar-extended source section, in a source quotient marking. -/
theorem source_star_steinberg_fixed
    {m : ℕ} (hm : 1 ≤ m) (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K]
    (B : Subgroup (Source.Hstar H)) (hB : ∀ b : B, b ^ 2 = 1)
    (hquad : ∀ (a b : B) v,
      (extendScalars K (starRepresentation H V₃ V₁ hn hk)) a
        ((extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v - v) =
      (extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v - v)
    (hker : Nat.card ((centralizer (Source.starImage H A : Set (Source.Hstar H))).subgroupOf B) ≤ 2048)
    (hsmall : ∀ b : B, operatorFixedCodim
      ((extendScalars K (starRepresentation H V₃ V₁ hn hk)) b) ≤ 2 * Nat.log 2 (Nat.card B)) :
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      let S := Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
        (Representation.asModule (markedExtendedComponentRepresentation hn hk hAH hHA K f))
        (SuzukiSmallDegree.tensorRep m K Finset.univ).asModule)
      ∀ (b : B) (v : S.toSubmodule),
        (extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v = v := by
  let ρ := extendScalars K (starRepresentation H V₃ V₁ hn hk)
  let D := Source.starImage H A
  let e₀ := sourceComponentStarEquiv hAH hHA
  let : D.Normal := sourceComponentStar_normal hHA
  obtain ⟨fD,hfix⟩ := SuzukiSmallDegree.ambient_steinberg_fixed ρ D B
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) m hm (e₀.symm.trans e)
    hB hquad hker hsmall
  let f := fD.symm.trans e₀.symm
  have he : f.trans e₀ = fD.symm := by
    apply MulEquiv.ext
    intro d
    exact e₀.apply_symm_apply (fD.symm d)
  have hR := sourceComponentStar_marked_representation hAH hHA hn hk K f
  rw [he] at hR
  change ρ.comp (D.subtype.comp fD.symm.toMonoidHom) =
    markedExtendedComponentRepresentation hn hk hAH hHA K f at hR
  refine ⟨f,?_⟩
  dsimp only at hfix ⊢
  rw [← hR]
  exact hfix
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
