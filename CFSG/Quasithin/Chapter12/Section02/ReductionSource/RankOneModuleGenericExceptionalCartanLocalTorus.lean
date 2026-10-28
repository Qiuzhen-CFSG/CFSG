module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBaumann
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The source torus reduction on the original Chapter 12 inputs

The escaping cubic and original right group generate the maximal A₇ local
join. The original Cartan normalizes the original Baumann subgroup, and
normalizes the maximal component exactly when its field degree is two.
The nonblock characteristic route thus leaves degree two or the literal
right block, on the unchanged Sylow and chosen-module inputs.
Both block exclusions, the remaining component sieve and source assembly
remain necessary; this is not the unconditional Cartan-escape theorem.
Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The literal original cubic generates the maximal local join with H. -/
theorem rankOne_local_cartan_cubic_sup_right
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    H ⊔ C = K ⊔ (T : Subgroup G) :=
  a.cubic_sup_right
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The actual Cartan-component normalizer condition is exactly degree two. -/
theorem rankOne_local_cartan_normalizes_iff_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    A ≤ normalizer (K : Set G) ↔ n = 2 :=
  a.cartan_normalizes_iff_degree_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) c d

/-- The source Cartan normalizes Baum(T), with no block premise. -/
theorem rankOne_local_cartan_normalizes_baumann
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) :=
  a.cartan_normalizes_baumann
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The original noncentral configuration has degree two or a right block. -/
theorem rankOne_local_cartan_noncentral_degree_two_or_right_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    n = 2 ∨ ChapterC.IsChiBlockIn (pResidual 2 H) :=
  localCartan_noncentral_degree_two_or_right_block
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
