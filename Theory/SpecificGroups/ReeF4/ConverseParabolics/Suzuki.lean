module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.CentralizerReduction
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.FullLeviRepresentation
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.RadicalAction
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.RadicalAction

/-!
# Full Suzuki-side Ree parabolic calculations

The specified root radical is nonidentity: the fixed end-root curve has an
injective field parameter, detected by an actual matrix entry. Relative
normality holds in the full parabolic, including its complementary torus.
The radical–Levi factorization and degree separation construct a retraction
onto the full fixed middle-node Levi, with exactly this radical as kernel.

The proved isomorphism of that full Levi with Suzuki matrices times field
units supplies a surjective parabolic projection with exactly the root
radical as its two-group kernel. The full-Levi action calculation, including
the complementary torus detected by an end-root coordinate, proves faithful
action on the radical abelianization and hence the intrinsic centralizer
bound. All these conclusions hold for `m ≥ 1` without an ambient simplicity
hypothesis or additional representation or action premises.

Sources: Aschbacher–Smith F.1.12(I)(5), printed p.263, and Theorem 0.1.2(1),
printed p.4 (`refs/quasithin.pdf`); GLS3 §§2.6 and 3.2 for the full parabolic.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics

open Subgroup LargeLocalSeeds BenderSuzuki.MatrixGroups
open Parabolics.OuterLocal.SuzukiCommutators
open SuzukiLevi (fullLevi ActsTriviallyOnRadicalAbelianization)

/-- The injective fixed end-root curve makes the actual radical nonidentity,
even at the binary parameter; no simplicity or order formula is needed. -/
theorem suzuki_radical_ne_bot (m : ℕ) : radical m .suzuki ≠ ⊥ := by
  let d := canonicalLocalBlockInput m
  intro hR
  have hstd : standardRadical d .suzuki = ⊥ :=
    (map_eq_bot_iff_of_injective _ d.modelEquiv.injective).mp
      ((standardRadical_map_eq d .suzuki).trans hR)
  have hseed : seedRadical d .suzuki = ⊥ := by
    rw [seedRadical, hstd, bot_subgroupOf]
  have hone : endRootElement d 1 = endRootElement d 0 := by
    rw [endRootElement_zero]
    exact mem_bot.mp (hseed ▸ endRootElement_mem_radical d 1)
  exact one_ne_zero (SuzukiRadicalAction.endRootElement_injective d hone)

/-- Both published seed calculations have their construction premises discharged.
This is self-centralization inside the seed only. -/
theorem suzuki_seedRadical_centralizer_le {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) :
    centralizer (seedRadical d .suzuki : Set (standardSeed d .suzuki)) ≤
      seedRadical d .suzuki :=
  suzuki_seedRadical_centralizer_le_of_projection hm d
    (SuzukiLeviProjection.projection d) (SuzukiLeviProjection.projection_surjective d)
    (SuzukiLeviProjection.projection_ker d)

/-- Extend a full-Levi representation through the actual radical retraction. -/
def suzukiProjectionOfLeviHom {m : ℕ}
    (ρ : fullLevi m →* SuzukiMatrixGroup m × (CoefficientField m)ˣ) :
    parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ :=
  ρ.comp (suzukiLeviRetraction m)

/-- Faithfulness on the full Levi identifies the projection kernel exactly. -/
theorem suzukiProjectionOfLeviHom_ker {m : ℕ}
    (ρ : fullLevi m →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ) :
    (suzukiProjectionOfLeviHom ρ).ker = intrinsicRadical m .suzuki := by
  unfold suzukiProjectionOfLeviHom
  rw [MonoidHom.ker_comp_of_injective _ _ hρ, suzukiLeviRetraction_ker]

/-- The full-parabolic projection has a two-group kernel once its faithful
full-Levi representation is supplied. -/
theorem suzukiProjectionOfLeviHom_ker_isPGroup {m : ℕ}
    (ρ : fullLevi m →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ) : IsPGroup 2 (suzukiProjectionOfLeviHom ρ).ker := by
  rw [suzukiProjectionOfLeviHom_ker ρ hρ]
  exact intrinsicRadical_isPGroup m .suzuki

/-- A general assembly from a faithful full-Levi representation and action.
The concrete instances are discharged by `suzuki_calculations` below. -/
theorem suzuki_calculations_of_fullLevi {m : ℕ}
    (ρ : fullLevi m →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ)
    (hfaithful : ∀ l ∈ fullLevi m,
      ActsTriviallyOnRadicalAbelianization m l → l = 1) :
    (∃ π : parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ,
      IsPGroup 2 π.ker) ∧
    radical m .suzuki ≠ ⊥ ∧
    parabolic m .suzuki ≤ normalizer (radical m .suzuki : Set (Model m)) ∧
    centralizer (intrinsicRadical m .suzuki : Set (parabolic m .suzuki)) ≤
      intrinsicRadical m .suzuki :=
  ⟨⟨suzukiProjectionOfLeviHom ρ, suzukiProjectionOfLeviHom_ker_isPGroup ρ hρ⟩,
    suzuki_radical_ne_bot m, suzuki_parabolic_le_radical_normalizer m,
    SuzukiLevi.centralizer_le_radical_of_faithful_fullLevi m hfaithful⟩

/-- The full Suzuki parabolic projects onto Suzuki matrices times the
complementary field torus. -/
def suzukiProjection {m : ℕ} (hm : 1 ≤ m) :
    parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ :=
  suzukiProjectionOfLeviHom (suzukiFullLeviEmbedding hm)

theorem suzukiProjection_surjective {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (suzukiProjection hm) :=
  (suzukiFullLeviEmbedding_surjective hm).comp (suzukiLeviRetraction_surjective m)

/-- The projection kills precisely the root-defined radical inside the parabolic. -/
theorem suzukiProjection_ker {m : ℕ} (hm : 1 ≤ m) :
    (suzukiProjection hm).ker = intrinsicRadical m .suzuki :=
  suzukiProjectionOfLeviHom_ker (suzukiFullLeviEmbedding hm)
    (suzukiFullLeviEmbedding_injective hm)

theorem suzukiProjection_ker_isPGroup {m : ℕ} (hm : 1 ≤ m) :
    IsPGroup 2 (suzukiProjection hm).ker :=
  suzukiProjectionOfLeviHom_ker_isPGroup (suzukiFullLeviEmbedding hm)
    (suzukiFullLeviEmbedding_injective hm)

/-- The projection required for odd-prime rank bounds in the full parabolic. -/
theorem exists_suzukiProjection {m : ℕ} (hm : 1 ≤ m) :
    ∃ π : parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ,
      IsPGroup 2 π.ker :=
  ⟨suzukiProjection hm, suzukiProjection_ker_isPGroup hm⟩

/-- Self-centralization inside the full parabolic, including its complementary
torus, with the full-Levi representation premise discharged. -/
theorem suzuki_intrinsicRadical_centralizer_le {m : ℕ} (hm : 1 ≤ m) :
    centralizer (intrinsicRadical m .suzuki : Set (parabolic m .suzuki)) ≤
      intrinsicRadical m .suzuki :=
  SuzukiLevi.RadicalAction.centralizer_le_radical_of_injective_representation hm
    (suzukiFullLeviEmbedding hm) (suzukiFullLeviEmbedding_injective hm)

/-- The complete Suzuki-side full-parabolic calculations used by the Ree
quasithin and even-characteristic converse. -/
theorem suzuki_calculations {m : ℕ} (hm : 1 ≤ m) :
    (∃ π : parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ,
      IsPGroup 2 π.ker) ∧
    radical m .suzuki ≠ ⊥ ∧
    parabolic m .suzuki ≤ normalizer (radical m .suzuki : Set (Model m)) ∧
    centralizer (intrinsicRadical m .suzuki : Set (parabolic m .suzuki)) ≤
      intrinsicRadical m .suzuki :=
  ⟨exists_suzukiProjection hm, suzuki_radical_ne_bot m,
    suzuki_parabolic_le_radical_normalizer m, suzuki_intrinsicRadical_centralizer_le hm⟩

end ReeF4.ConverseParabolics
