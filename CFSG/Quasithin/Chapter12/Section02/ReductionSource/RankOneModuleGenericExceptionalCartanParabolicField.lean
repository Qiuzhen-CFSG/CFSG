module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicLinear
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Comparing the selected parabolic with the original rank-two residual

The original Chapter12 input places the selected right factor locally at
a full Sylow of the residual. The symplectic point/plane calculation then
identifies its literal two-core quotient over the residual's field.
An A₅ quotient forces that field to have four elements and constructs the
prescribed Hall subgroup B as E₉. At original degree two this proves the
residual normalization conclusion from local control. In the projective
linear row, the same A₅ quotient forces PSL₃(4), which the original source
hypothesis excludes. Both rows therefore give normalization in original
degree two, and the actual nonzero-core prime application derives the
required strictness from the escaping actor.

The selected factor need not be a C-component of H. The original residual
model remains explicit; the Cartan local-to-global owner retains source
selection and the other model, degree, and zero-core branches.
Source: Aschbacher–Smith 5.1.10 and 5.2.2, pp.634,648–649,
applied to 12.2.2 on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The actual A₅ parabolic constructs Sp₄(4) and the literal Hall plane;
the escaping actor is quintic by the original quasithin rank bound. -/
theorem rankOne_prime_A5_symplectic_parabolic_hall
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    f = 2 ∧ ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧ p = 5 :=
  d.A5_right_symplectic_prime_hall (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen c hd hz hf hm hA5

/-- Degree-two residual normalization with the selected A₅ parabolic,
without a field-marking or field-divisibility premise. -/
theorem rankOne_cartan_normalizes_of_A5_symplectic_parabolic_degree_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {R : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hR : R < residual H) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    A ≤ normalizer (residual H : Set G) :=
  d.cartan_normalizes_of_A5_symplectic_degree_two
    (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl)
    hH hgen c hcontrol hR hf hm hA5

/-- Both projective rank-two residual rows normalize the original degree-two
Cartan when its selected parabolic has the A₅ quotient. -/
theorem rankOne_cartan_normalizes_of_A5_projective_parabolic_degree_two
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
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    A ≤ normalizer (residual H : Set G) :=
  d.cartan_normalizes_of_A5_projective_rankTwo_degree_two
    (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl)
    hH hgen hthree c hcontrol hR hf hm hA5

/-- The actual escaping actor supplies strictness in the nonzero-core branch;
no separate proper-parabolic premise remains on this exclusion. -/
theorem rankOne_prime_A5_projective_parabolic_excluded_degree_two
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
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False :=
  d.A5_projective_rankTwo_prime_excluded_degree_two
    (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl)
    hH hgen hthree c hcontrol hd hz hf hm hA5

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
