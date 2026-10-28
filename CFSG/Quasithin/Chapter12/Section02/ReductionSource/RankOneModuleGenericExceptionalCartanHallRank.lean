module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Exchanged Cartan normalization on the chosen Chapter12 module

The actual right Hall subgroup has rank at most one at the prime of an
escaping left actor. On a marked exchanged linear component, this rules
out any actor prime dividing its torus order. In original left degrees
two and four, divisibility of the marked right degree by the left degree
therefore proves normalization of the literal residual from local control.
Both field parameters and the source quotient map are retained.

Source: Aschbacher--Smith 5.1.10(1), 5.2.2 and 12.2.2,
printed pp.634,646--649,795. The other source rows remain with the
Cartan local-to-global owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- An escaping actor bounds the rank of the original Hall and overlap,
without a right-factor selection or a field-degree comparison. -/
theorem rankOne_prime_right_hall_rank
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    B ≤ centralizer (D : Set G) ∧ Disjoint D B ∧ primeRank p B ≤ 1 ∧
      primeRank p (normalizer (L : Set G) ⊓ H : Subgroup G) ≤ 1 := by
  have hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨c.centralizes_prime_actor hi hd, hd.disjoint_right_cartan c hH.1.1.1,
    c.right_primeRank_le_one hi hd hH.1.1.1,
    c.overlap_primeRank_le_one hi hd hH.1.1.1⟩

/-- This exchanged linear source branch supplies the actual normalization
conclusion, rather than a remaining local normalization premise. -/
theorem rankOne_cartan_normalizes_of_exchanged_linear_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hsmall : n = 2 ∨ n = 4) (hnf : n ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany hn hpsl).cartan_normalizes_of_exchanged_linear_small_degree
    hH c hcontrol hsmall hnf hC hqs hc hF hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
