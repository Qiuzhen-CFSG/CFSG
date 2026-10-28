module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors

/-!+# Earlier source inputs for the solvable case of 13.8.5

These are universal earlier implications, stated before selecting H, its
representation, or a transvection. The local model clauses retain actual
equivariant A₆ or hexacode-cover models: the point coordinates are used by
the two-factor theorem, and the augmentation coordinates and full flag by
the one-factor theorem. Neither clause assumes a factor placement, a
residual alternative, or a moved space for the transvection closure.

The remaining clauses are precisely the consumed earlier local facts:
13.2.2(3),(9), 13.5.5, the centralizer identity F.9.2(3) recalled on p.946,
and V₁=[V₃,Q_H] from 13.7.3(6). In particular, full generation of V₃ by
L₁-commutators is not an input. The source normalizer bound 13.5.5 retains
M_V=N_M(V), and the L₀ bound requires the actual covered quotient.

This interface does not prove those earlier theorems. The solvable-case
theorem is conditional on them, as on the separate universal B.1.8 input.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.877, 915–916, 935–936, 946–948.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable
variable {G : Type*} [Group G] [Finite G]

/-- The consumed earlier local results, universal in the standing setup.
The full solvable-case implication is a theorem using these results, not
a field of this interface. -/
structure EarlierLocalInputs : Prop where
  point_models : TwoFactors.EarlierMarkedModels (G := G)
  natural_models : ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G),
    LocalSetup T L V V₁ V₂ V₃ M G₁ →
      Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
      Nonempty (NaturalSetup L (T : Subgroup G) V V₁ V₃)
  covered_factorization : ∀ (L T V W₁ W₃ : Subgroup G),
    NaturalSetup L T V W₁ W₃ → one L T W₁ = plus L T W₁ ⊔ zero L
  covered_normalizer : ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G),
    LocalSetup T L V V₁ V₂ V₃ M G₁ →
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      normalizer (zero L : Set G) ≤ M
  flag_normalizers : ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G),
    LocalSetup T L V V₁ V₂ V₃ M G₁ →
      normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤
        M ⊓ normalizer (V : Set G)
  centralizer : ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G),
    LocalSetup T L V V₁ V₂ V₃ M G₁ → ∀ H : Subgroup G,
    H ∈ Source.Hz (sourceOne L T V₁) T G₁ M →
      commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H
  core_displacement : ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G),
    LocalSetup T L V V₁ V₂ V₃ M G₁ → ∀ H : Subgroup G,
    H ∈ Source.Hz (sourceOne L T V₁) T G₁ M → V₁ = ⁅V₃, Source.QH H⁆

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable

end
