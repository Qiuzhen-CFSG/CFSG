module

public import Theory.GroupTheory.WreathTwoOddCoreImageDichotomy
public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.PGroup.IndexTwoOmegaCenter
public import Theory.GroupAction.FixedLineIrreducibility
public import Theory.GroupTheory.IntersectingConjugateFusion
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.SourceControls
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Source
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.SeedSource
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.PlaneSource
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Source
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OriginalSource
public import CFSG.Quasithin.Chapter14.Section02.SourceSetup
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import CFSG.Quasithin.Chapter14.Section02.LargeSource
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import CFSG.Quasithin.Chapter14.Section02.LargeBenderSource
public import CFSG.Quasithin.Chapter14.Section02.LargeAmalgamSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource

/-!
# The wreath-product elimination in Section 15.3

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Section 15.3, pp. 1120--1155. Theorem 15.3.1
asserts that a group satisfying Hypothesis 14.1.5 is isomorphic to `J₂`,
`J₃`, `³D₄(2)`, the Tits group, `G₂(2)'`, or `M₁₂`. Theorem 15.1.3 reduces
its proof to the natural four-dimensional orthogonal action of
`M_f / C_{M_f}(V(M_f))`. The contradiction ends on p.1155 (PDF p.1172).

The imports provide the exact local constructions, the index-two central
omega argument for 15.3.8, the fixed-line irreducibility argument for
15.3.57(1), the intersection-fusion argument for 15.3.62(2), and the
normal-closure action-kernel calculation in the final paragraph.
Each argument still requires its stated local inputs from the section.
The terminal source leaf retains the S₃ residual and centralization
alternative, and otherwise assembles the exceptional six-dimensional
action and both actual ambient definite-plane normalizer A₅ quotients.
Its inputs are the earlier local geometry, singular-line span and corrected
classification witnesses; no recognized-model or coordinate premise remains.
The terminal endgame eliminates both alternatives using the earlier singular
normalizer control, the definite-plane normalizer bound, solvability of M,
and the escape of X_E.

The auxiliary wreath calculations below concern the literal regular wreath
product `SL₂(2) ≀ C₂`. They neither identify the natural module nor prove
the source elimination. The uniqueness theorems, the abelianness of
`⟨V^{M_c}⟩`, the final Goldschmidt configuration, the earlier local inputs
and classifier discharge remain necessary for assembly of Theorem 15.3.1.
-/

namespace CFSG.Quasithin.Chapter15.Section03

open Theory.GroupTheory

public abbrev S3Wreath :=
  RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (Multiplicative (ZMod 2))

/-- The concrete quotient shadow in §15.3, written as the regular wreath model.
The first factor is `SL₂(2)`, which is the symmetric group on three letters. -/
public abbrev section03Wreath := S3Wreath

/-- Auxiliary odd-core calculation: the odd core of the wreath shadow has
index eight.  The equivalence is an actual group isomorphism supplied by the
local recognition step. -/
public theorem section03_oddCore_index_eight
    {K : Type*} [Group K] [Finite K]
    (model : Nonempty (K ≃* section03Wreath)) :
    (pPrimeCore 2 K).index = 8 := by
  exact wreathTwo_oddCore_index_eight model

/-- The same index statement for the quotient occurring in the source
notation `M_f / C_{M_f}(V(M_f))`. -/
public theorem section03_quotient_oddCore_index_eight
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (model : Nonempty ((G ⧸ N) ≃* section03Wreath)) :
    (pPrimeCore 2 (G ⧸ N)).index = 8 := by
  exact section03_oddCore_index_eight model

/-- Auxiliary kernel dichotomy. For every homomorphism out of the wreath
shadow, either the odd core is contained in its kernel or the image has order
divisible by nine. -/
public theorem section03_oddCore_kernel_dichotomy
    {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y]
    (model : Nonempty (K ≃* section03Wreath)) (f : K →* Y) :
    pPrimeCore 2 K ≤ f.ker ∨ 9 ∣ Nat.card f.range := by
  exact wreathTwo_oddCore_le_ker_or_nine_dvd_range model f

/-- A faithful map out of the wreath shadow has image order divisible by nine. -/
public theorem section03_faithful_image_dvd_nine
    {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y]
    (model : Nonempty (K ≃* section03Wreath)) (f : K →* Y)
    (hf : Function.Injective f) :
    9 ∣ Nat.card f.range := by
  rcases section03_oddCore_kernel_dichotomy model f with hcore | hdiv
  · have hker : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr hf
    have hcorebot : pPrimeCore 2 K = ⊥ := le_bot_iff.mp (hker ▸ hcore)
    have hcard : Nat.card (pPrimeCore 2 K) = 9 := by
      have hindex := section03_oddCore_index_eight model
      have hcardK : Nat.card K = 72 := by
        obtain ⟨e⟩ := model
        exact (Nat.card_congr e.toEquiv).trans (by
          rw [RegularWreathProduct.card]
          have hsl2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
            rw [Nat.card_eq_fintype_card]
            decide
          rw [hsl2]
          norm_num [Nat.card_eq_fintype_card])
      have hmul := (pPrimeCore 2 K).card_mul_index
      rw [hcardK, hindex] at hmul
      omega
    rw [hcorebot, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exact hdiv

end CFSG.Quasithin.Chapter15.Section03
