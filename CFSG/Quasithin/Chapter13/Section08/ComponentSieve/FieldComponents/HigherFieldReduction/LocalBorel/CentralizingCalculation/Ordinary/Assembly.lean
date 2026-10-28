module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.LocalCalculation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Inverter
public import Theory.Representation.HexacodeAction.CubicLocalModel.Normalizer

/-!
# The ordinary local calculation with both two-kernels

For the unchanged source context and ordinary natural setup, the actual
action of J = BL₁ has the inner natural A₄ image. Its kernel gives
J = CL₁, where C is the literal centralizing residual. The intrinsic
natural-action centralizer calculation proves C ≤ C_M(V). The cubic
quotient of L₁ then gives [J : C O₂(J)] = 3 and O²(O³(B)) ≤ C.

The permitted abelian-Borel input, together with the proved two-perfectness
of B, makes B/O₂(B) odd. Hence O³(B) = O²(O³(B)) O₂(B), giving the
saturated residual containment required by the torus adapter. The genuine
natural Sylow action constructs t in T ∩ L inverting L₁/O₂(L₁); this
same t normalizes both B and J and fixes C/O₂(C).

All model-image, centralizer and inverter premises of the earlier local
reductions are discharged here. The sole additional input is
[B,B] ≤ O₂(B), supplied by the independent model-Borel calculation to the
parent assembly. Relative normality, both two-perfectness statements,
O₂(L₁) ≤ O₂(J), and C ≠ J are proved in the re-exported TwoKernels
module; no covered-only factorization from 13.2.2(3) is used.

Source: Aschbacher–Smith 13.8.20, printed p.954/PDF p.971. This is the
sufficient calculation with the two distinct kernels, as specified by the
6 October 2026 source repair. It does not assert the incompatible printed
pair C = O³(B), [J : C O₂(B)] = 3; its diagnostic and all original
conditional APIs remain unchanged. The parent retains the torus transfer
and final ordinary/covered assembly.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Assembly

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁)

/-- B is normal relative to the actual product J. -/
theorem product_normalizes_borel :
    d.B ⊔ one L (T : Subgroup G) V₁ ≤ normalizer (d.B : Set G) :=
  sup_le d.B.le_normalizer (le_sup_left.trans d.borel_normalized)

/-- The intrinsic natural-A₆ calculation gives centralization of all V. -/
theorem centralizingResidual_le_centralizer :
    centralizingResidual d.B (one L (T : Subgroup G) V₁) L ≤
      M ⊓ centralizer (V : Set G) :=
  Centralization.centralizingResidual_le_of_natural_centralizer d
    Representation.Hexacode.CubicLocalModel.naturalAlternating_centralizer

include a in
/-- Retain the actual natural-action inverter, including both normalizations
and displacement into the intrinsic core of C. No power of t is taken. -/
theorem exists_marked_inverter :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∈ L ∧
      InvertsTwoCoreQuotient (one L (T : Subgroup G) V₁) t ∧
      t ∈ normalizer (d.B : Set G) ∧
      t ∈ normalizer ((d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) : Set G) ∧
      ⁅centralizingResidual d.B (one L (T : Subgroup G) V₁) L, zpowers t⁆ ≤
        (centralizingResidual d.B (one L (T : Subgroup G) V₁) L).pCoreIn 2 := by
  obtain ⟨t, ht, htL, hinv⟩ := Inverter.exists_marked_inverter a
  obtain ⟨htB, htJ⟩ := TwoKernels.marked_normalizes d t ht
  exact ⟨t, ht, htL, hinv, htB, htJ,
    centralizingResidual_commutator_core _ _ _ d.product_normalizes_L t htL htJ⟩

/-- The ordinary branch of the sufficient local calculation. All local action,
factorization, centralization, residual, index and inverter conclusions are
derived; only the independent abelian-Borel premise remains explicit. -/
theorem local_calculation (hab : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2) :
    let X := one L (T : Subgroup G) V₁
    let C := centralizingResidual d.B X L
    let J := d.B ⊔ X
    let R := residualIn 2 (residualIn 3 d.B)
    Nat.card (Action.modelAction d a).range = 12 ∧
      J = C ⊔ X ∧
      C ≤ M ⊓ centralizer (V : Set G) ∧
      R ≤ C ∧
      Odd (Nat.card (d.B ⧸ pCore 2 d.B)) ∧
      residualIn 3 d.B = R ⊔ d.B.pCoreIn 2 ∧
      residualIn 3 d.B ≤ C ⊔ d.B.pCoreIn 2 ∧
      (C ⊔ J.pCoreIn 2).relIndex J = 3 ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∈ L ∧
        InvertsTwoCoreQuotient X t ∧
        t ∈ normalizer (d.B : Set G) ∧
        t ∈ normalizer (J : Set G) ∧
        ⁅C, zpowers t⁆ ≤ C.pCoreIn 2 :=
  ⟨ModelImage.action_range_card d a,
    LocalCalculation.factorization d a,
    centralizingResidual_le_centralizer d,
    LocalCalculation.iterated_residual_le d a,
    TwoKernels.borel_quotient_odd d hab,
    TwoKernels.borel_threeResidual d hab,
    LocalCalculation.saturated_residual_le d a hab,
    LocalCalculation.cubic_index d a,
    exists_marked_inverter d a⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Assembly
