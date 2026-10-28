module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.FullProduct.External
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.ModelBorel

/-!+# The covered source calculation in the full product BL₁

Put D = L₁, X = L₁,+, Z = L₀, C = O²(C_{BD}(L/O₂(L))), and J = BD.
The genuine covered model gives J = CD. The earlier factorization D = XZ
and the proved inclusion Z ≤ C give J = CX. The full-product calculation
then supplies relative normality of B and C, both two-perfectness results,
O₂(X) ≤ O₂(D) ≤ O₂(J), C ≠ J, O²(O³(B)) ≤ C, and [J : C O₂(J)] = 3.
These structural results are re-exported from `ZeroPlacement.FullProduct`.

Here the actual natural-action kernel gives C ≤ C_M(V), and the uniform
model-Borel theorem discharges the abelian quotient premise in
O³(B) = O²(O³(B)) O₂(B) ≤ C O₂(B). The marked inverter is kept as the
same element of T ∩ L, together with its fixation of Z/O₂(Z), its
normalization of B and J, and [C,⟨t⟩] ≤ O₂(C). No power of t is taken.

The parent centralizing calculation uses N = C O₂(J) to transfer these
conclusions to torus fixation and the cyclic commutator bound. Its index
comparison uses BD = J, while X is the marked cubic subgroup. The
re-exported `FullProduct.External` adapter retains the actual star-map
kernel; its T*-centralizing inverter is constructed by the separate
source-alternative assembly before the external conclusion is used.

This is the sufficient full-product route for Aschbacher–Smith 13.8.20,
printed p.954/PDF p.971, using Notation 13.2.1, 13.2.2(3), and 13.7.3(9).
It preserves the literal residuals and all earlier conditional APIs.
It does not prove the stronger residual identity C = O³(B)Z or placement
C ≤ BX. Import this extension near the source consumer, never into Covered.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.SourceCalculation

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)

local notation "D" => one L (T : Subgroup G) V₁
local notation "X" => plus L (T : Subgroup G) V₁
local notation "C" => centralizingResidual d.B D L
local notation "J" => (d.B ⊔ D : Subgroup G)

/-- The full natural-action kernel centralizes V; the source product lies in M. -/
theorem centralizingResidual_le_centralizer : C ≤ M ⊓ centralizer (V : Set G) :=
  le_inf (centralizingResidual_le_M _ _ _ _ d.borel_in_M d.one_le_M)
    (ZeroPlacement.FullProduct.External.centralizingResidual_le_centralizer d)

/-- The actual higher-field model discharges the Borel quotient premise. -/
theorem borel_commutator_le_twoCore : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2 :=
  ModelBorel.borel_commutator_le_twoCore H K (T : Subgroup G)
    d.component_le d.sylow_H d.model d.degree

/-- Separate two-perfectness of B makes its abelian quotient odd. -/
theorem borel_quotient_odd : Odd (Nat.card (d.B ⧸ pCore 2 d.B)) :=
  odd_card_quotient_twoCore_of_isPPerfect d.B
    (ZeroPlacement.FullProduct.borel_isPPerfect d) (borel_commutator_le_twoCore d)

/-- The residual supplement now has no additional abelian-quotient premise. -/
theorem borel_threeResidual :
    residualIn 3 d.B = residualIn 2 (residualIn 3 d.B) ⊔ d.B.pCoreIn 2 :=
  ZeroPlacement.FullProduct.borel_threeResidual d (borel_commutator_le_twoCore d)

include a hfactor in
/-- The sufficient source containment retains the intrinsic two-core of B. -/
theorem borel_threeResidual_le : residualIn 3 d.B ≤ C ⊔ d.B.pCoreIn 2 :=
  ZeroPlacement.FullProduct.borel_threeResidual_le d a hfactor
    (borel_commutator_le_twoCore d)

include a hfactor in
/-- The original inverter, its zero-mark fixation, and both normalizations.
Normalization of B uses the source Borel assertion independently of that of J. -/
theorem exists_marked_inverter :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient X t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      t.val ∈ normalizer (d.B : Set G) ∧
      t.val ∈ normalizer (J : Set G) ∧
      ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 := by
  obtain ⟨t, hinv, hzero, hcomm⟩ := Covered.exists_marked_inverter d a hfactor
  exact ⟨t, hinv, hzero, d.borel_normalized (mem_sup_right t.property.1),
    d.T_normalizes_product t.property.1, hcomm⟩

include a hfactor in
/-- The complete covered local batch for the parent torus calculation.
All local model, centralizer, residual, index and inverter assertions are
proved from the unchanged source data and exact earlier factorization. -/
theorem local_calculation :
    J = C ⊔ D ∧
      J = C ⊔ X ∧
      C ≤ M ⊓ centralizer (V : Set G) ∧
      C ≤ J ∧
      ((C).subgroupOf J).Normal ∧
      (d.B.subgroupOf J).Normal ∧
      (X).pCoreIn 2 ≤ (D).pCoreIn 2 ∧
      (D).pCoreIn 2 ≤ (J).pCoreIn 2 ∧
      IsPPerfect 2 d.B ∧
      IsPPerfect 2 (J : Subgroup G) ∧
      C ≠ J ∧
      residualIn 2 (residualIn 3 d.B) ≤ C ∧
      ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2 ∧
      residualIn 3 d.B = residualIn 2 (residualIn 3 d.B) ⊔ d.B.pCoreIn 2 ∧
      residualIn 3 d.B ≤ C ⊔ d.B.pCoreIn 2 ∧
      (C ⊔ (J).pCoreIn 2).relIndex J = 3 ∧
      zero L ≤ C ∧
      residualIn 2 (C ⊓ D) = zero L ∧
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        InvertsTwoCoreQuotient X t.val ∧
        coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
        t.val ∈ normalizer (d.B : Set G) ∧
        t.val ∈ normalizer (J : Set G) ∧
        ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 :=
  ⟨ModelImage.product_eq d a hfactor,
    ZeroPlacement.FullProduct.product_eq d a hfactor,
    centralizingResidual_le_centralizer d,
    centralizingResidual_le _ _ _,
    ZeroPlacement.FullProduct.centralizingResidual_normal d,
    ZeroPlacement.FullProduct.borel_normal d,
    ZeroPlacement.FullProduct.plus_core_le_one_core a,
    ZeroPlacement.FullProduct.one_core_le_product_core d,
    ZeroPlacement.FullProduct.borel_isPPerfect d,
    ZeroPlacement.FullProduct.product_isPPerfect d,
    ZeroPlacement.FullProduct.centralizingResidual_ne_product d a hfactor,
    ZeroPlacement.FullProduct.borel_two_threeResidual_le d a hfactor,
    borel_commutator_le_twoCore d,
    borel_threeResidual d,
    borel_threeResidual_le d a hfactor,
    ZeroPlacement.FullProduct.cubic_index d a hfactor,
    Covered.source_zero_le d hfactor,
    Covered.source_residual_intersection d hfactor,
    exists_marked_inverter d a hfactor⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.SourceCalculation
