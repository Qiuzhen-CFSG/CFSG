module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCover
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The special-linear cover in the original Cartan normalization argument

The intrinsic residual quotient supplies a Sylow normalizer with full
rank-two torus quotient inside the original overlap. The escaping-actor
rank bound proves normalization when the original degree is two or four
and divides the residual field degree. A selected A₅ parabolic forces
the special-linear residual field to be four, so this closes the original
degree-two branch in all three rank-two rows, retaining SL₃ separately
from PSL₃. In the nonzero-core prime configuration properness is derived
from the actual escaping actor.

The general source selection, higher fields and zero-core branches remain
with the Cartan local-to-global assembly; no selected parabolic is
identified with an H-component.
Source: Aschbacher–Smith 5.2.2, pp.648–649, applied to 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The actual special-linear residual torus supplies the normalization
conclusion at either original small degree dividing its field degree. -/
theorem rankOne_cartan_normalizes_of_specialLinear_residual_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : n = 2 ∨ n = 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hf : 1 < f) (hnf : n ∣ f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by omega) hpsl).cartan_normalizes_of_specialLinear_residual_small_degree
    hH c hcontrol hn hf hnf hm

/-- The actual selected A₅ parabolic in a special-linear residual forces
the four-element field and a quintic escaping actor. -/
theorem rankOne_prime_A5_specialLinear_field_and_prime
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : f = 2 ∧ p = 5 :=
  d.A5_right_specialLinear_prime (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hz hf hm hA5

/-- Original degree-two normalization in all rank-two residual rows, including
SL₃ with its scalar centre, for the selected A₅ parabolic. -/
theorem rankOne_cartan_normalizes_of_A5_rankTwo_parabolic_degree_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {R : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hR : R < residual H) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    A ≤ normalizer (residual H : Set G) :=
  d.cartan_normalizes_of_A5_rankTwo_degree_two
    (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl)
    hH hgen hthree c hcontrol hR hf hm hA5

/-- The literal nonzero-core prime configuration supplies the proper-parabolic
premise, excluding all three rank-two rows in original degree two. -/
theorem rankOne_prime_A5_rankTwo_parabolic_excluded_degree_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {R : Subgroup G} (d : Prime.LocalData T L H B D R)
    {p : ℕ} (hd : CartanPrimeActor A H p D)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False :=
  d.A5_rankTwo_prime_excluded_degree_two
    (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl)
    hH hgen hthree c hcontrol hd hz hf hm hA5

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
