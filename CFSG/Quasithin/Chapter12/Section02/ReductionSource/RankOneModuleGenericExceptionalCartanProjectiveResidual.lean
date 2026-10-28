module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalProjectiveResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Projective split-torus normalization in the chosen-module setup

The original chosen module supplies the complete rank-one input. The
projective residual torus keeps its cubic scalar quotient. A prime actor
therefore must be cubic and the residual degree cannot be divisible by six
when the original degree divides it. If the original degree is two, four
or eight and the residual degree is also divisible by three, local control
gives the actual Cartan normalization conclusion. Combining with the
existing SL₃ and Sp₄ proofs treats all diagram covering alternatives.

The general local-to-global assembly, other field degrees, diagram
parabolic selection, zero-core exclusions and changed-Sylow cases remain
with qt-d-1222-rankone-cartan-local-to-global. These are specialized source
branches, not a replacement for its original conditional theorem.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, printed pp.646–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (M : ChosenModule T L V)
include M

/-- The original prime actor in a projective residual is cubic, and the
marked field degree is not divisible by six. -/
theorem rankOne_cartan_projective_residual_prime_constraints
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) {D : Subgroup G} (hd : CartanPrimeActor A H p D)
    (hf : 1 < f) (hnf : n ∣ f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    p = 3 ∧ ¬ 9 ∣ 2 ^ f - 1 ∧ ¬ 6 ∣ f :=
  c.projective_residual_prime_constraints
    (M.rankOne_generic_input_of_many h hmany hn hpsl) hd hH hf hnf hm

/-- Normalization of the literal residual at all three original small degrees. -/
theorem rankOne_cartan_normalizes_of_projective_residual_cubic_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hf : 1 < f) (hnf : n ∣ f) (h3 : 3 ∣ f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by omega) hpsl).cartan_normalizes_of_projective_residual_cubic_degree
    hH c hcontrol hn hf hnf h3 hm

/-- The original diagram marking discharges the residual-model alternatives
in this normalization branch. -/
theorem rankOne_cartan_normalizes_of_diagram_cubic_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hnf : n ∣ f) (h3 : 3 ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by omega) hpsl).cartan_normalizes_of_diagram_cubic_degree
    hH hpar c hcontrol hn hnf h3 hC hqs hc hf hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
