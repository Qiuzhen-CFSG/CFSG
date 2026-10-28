module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourceSteinbergCoordinates
public import Theory.Representation.BinaryOffender.ScalarExtensionBudget

/-!
# The original binary budget fixes the scalar-extended Steinberg part

Transfer quadraticity and each operator's displacement bound from the binary
source section U_H/V₁. The resulting application retains the same original
actor B and the literal centralizer subgroup in H/O₂(H).

Source: Aschbacher–Smith §13.6, printed pp.934–935.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative TensorProduct MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Section08 Ratio BenderSuzuki.MatrixGroups Representation Module
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
variable {G : Type*} [Group G] [Finite G]
  {V₁ V₃ H A : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))
local instance sourceBudgetCommGroup : CommGroup (Source.UH H V₃) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The actual small-ratio actor fixes the canonical full Steinberg part of
the original scalar-extended source section, in a source quotient marking. -/
theorem source_star_steinberg_fixed_of_binary_budget
    {m : ℕ} (hm : 1 ≤ m) (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K]
    (B : Subgroup (Source.Hstar H)) (hB : ∀ b : B, b ^ 2 = 1)
    (hquad : IsQuadratic (starRepresentation H V₃ V₁ hn hk) B)
    (hker : Nat.card ((centralizer (Source.starImage H A : Set (Source.Hstar H))).subgroupOf B) ≤ 2048)
    (hsmall : fixedCodim (starRepresentation H V₃ V₁ hn hk) B ≤ 2 * rank B) :
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      let S := Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
        (Representation.asModule (markedExtendedComponentRepresentation hn hk hAH hHA K f))
        (SuzukiSmallDegree.tensorRep m K Finset.univ).asModule)
      ∀ (b : B) (v : S.toSubmodule),
        (extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v = v := by
  exact source_star_steinberg_fixed hn hk hAH hHA hm e K B hB
    (hquad.extendScalars (F := K)) hker
    (extendScalars_operatorFixedCodim_le_of_fixedCodim _ B hsmall)
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
