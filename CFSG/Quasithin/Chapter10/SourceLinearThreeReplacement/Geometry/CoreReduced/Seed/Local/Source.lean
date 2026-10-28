module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local.Primes
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Source
public import Theory.GroupTheory.MinimalParabolicResidual

/-!
# The original diagonal seed calculation

The actual diagonal parabolic P=C_{L₀T}(ab) has quotient S₃ wr C₂,
so its Sylow subgroup T is maximal. Its two-core preserves L by the
natural-action calculation. Thus a T-normal subgroup R outside T₁ lies
outside O₂(P), and the unique-maximal-overgroup residual theorem gives
[O²(P),R]=O²(P). The existing restriction theorem identifies O²(P)
with the literal seed X=O²(C_{L₀}(ab)), through the original inclusions.

Together with prime support and the nontrivial cubic quotient, this
proves LocalCalculationAt without additional premises. The final
SeedAnalysis application retains only the independent module-generation
input, whose discharge belongs to the seed assembly owner.

Source: Aschbacher--Smith 10.1.3 and 10.2.11, printed pp.742,753--754;
the structural residual argument is B.6.8(6d), printed p.115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local
open Overgroups.Closure.Parabolic
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- Every original T-normal subgroup outside T₁ generates X by commutators. -/
theorem commutator (c : Configuration s a b) (R : Subgroup G)
    (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hout : ¬ R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    ⁅centralizerSeed T L (a*b),R⁆ = centralizerSeed T L (a*b) := by
  let P := diagonalParabolic T L (a*b)
  have hTP : (T : Subgroup G) ≤ P := sylow_le_diagonalParabolic c.central
  have hRP : R ≤ P := hRT.trans hTP
  let S := T.subtype hTP
  have hmax := WreathTwoResidual.sylow_isCoatom_of_core_quotient S (parabolicQuotient c)
  have hu : Order.HasUniqueMaximalOver (S : Subgroup P) ⊤ := by
    refine ⟨lt_top_iff_ne_top.mpr hmax.ne_top,(S : Subgroup P),⟨le_rfl,hmax.covBy_top⟩,?_⟩
    intro M hM
    rcases eq_or_lt_of_le hM.1 with h | h
    · exact h.symm
    · exact (hM.2.ne (hmax.2 _ h)).elim
  have hnot : ¬ R.subgroupOf P ≤ pCore 2 P := by
    intro h
    apply hout
    intro r hr
    exact parabolic_core_le_stabilizer c ⟨⟨r,hRP hr⟩,h hr,rfl⟩
  have hn : (S : Subgroup P) ≤ normalizer (R.subgroupOf P : Set P) := by
    rw [← subgroupOf_normalizer_eq hRP]
    exact fun x hx => hTR hx
  have he := commutator_twoResidual_eq_of_normal_sylow_subgroup S hu
    (R.subgroupOf P) (fun _ hx => hRT hx) hn hnot
  have hh := congrArg (map P.subtype) he
  rw [map_commutator,diagonalParabolic_residual,map_subgroupOf_eq_of_le hRP] at hh
  exact hh

/-- All three calculations for the same original source configuration. -/
theorem localCalculation (c : Configuration s a b) : LocalCalculation c where
  prime_spectrum := prime_spectrum c
  not_two := not_two c
  commutator := commutator c

/-- The complete local calculation, without a core, action, or recognition premise. -/
theorem localCalculationAt (T : Sylow 2 G) : LocalCalculationAt T := by
  intro L D s a b c
  exact localCalculation c

/-- The actual seed consumer now retains only the independent module calculation. -/
theorem seedAnalysisAt_of_moduleGeneration (hmodule : ModuleGenerationAt T) : SeedAnalysisAt T :=
  seedAnalysisAt_of_calculations (localCalculationAt T) hmodule

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local
