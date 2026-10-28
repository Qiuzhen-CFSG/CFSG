module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreJanko
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanZeroCore

/-!
# Marked zero-core exclusions for the literal Chapter 12 prime pair

The original selected factor now excludes both Hall–Janko parabolic
models. A binary-triality right-parabolic marking forces the original
left field degree to two. Its actual center is the original omega-center,
centralized by H, and its seven-subgroup fixes the whole original L-span.

The construction of the source prime pair is discharged. Marked recognition,
the remaining triality and unitary exclusions, higher-field reduction and
changed-Sylow assembly remain with qt-d-1222-rankone-cartan-local-to-global.
No normalization theorem is asserted by these model reductions.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, printed pp.647–648,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The actual source construction yields a prime pair whose zero-core branch
admits neither of the two genuine Hall–Janko parabolic models. -/
theorem rankOne_cartan_source_zeroCore_not_hallJanko
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧
      ((generated L H D R).pCoreIn 2 = ⊥ →
        ¬ ChapterF.GreenBook.HallJanko.IsJ2ParabolicModel (zeroCoreAmalgam L H B D R) ∧
        ¬ ChapterF.GreenBook.HallJanko.IsAutJ2ParabolicModel (zeroCoreAmalgam L H B D R)) := by
  let hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d⟩ := source_prime_pair hi hH hpar hthree c hd
  exact ⟨R,d,fun hz => ⟨d.zeroCore_not_janko_parabolic hi hH c hd hz,
    d.zeroCore_not_autJanko_parabolic hi hH c hd hz⟩⟩

/-- The literal marked triality row has original degree two and cubic whole
left Cartan; its actual seven-subgroup fixes the original omega-module. -/
theorem rankOne_cartan_zeroCore_binaryTriality_reduction
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R : Subgroup G} (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    n = 2 ∧ p = 3 ∧ D = A ∧
      (center (Global.sourceS L H)).map (Global.sourceS L H).subtype =
        Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      H ≤ omegaCentralizer T ∧
      (B ⊓ R : Subgroup G) ≤ centralizer
        (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  let hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  have hdegree := d.binaryTriality_original_degree hi e.right
  have hp := (d.zeroCore_binaryTriality_configuration hi hH c hd hz e).1
  have hA : Nat.card A = 3 := by
    have hh := c.left_card hpsl hi.sylow_normalizes
    norm_num [hdegree] at hh
    exact hh
  have hDA : D = A := eq_of_le_of_card_ge hd.le_cartan (by rw [hA,hd.card,hp])
  obtain ⟨hcenter,hcard,hcentral⟩ := d.zeroCore_binaryTriality_omega_center hi hH c hd hz e
  exact ⟨hdegree,hp,hDA,hcenter,hcard,hcentral,
    d.zeroCore_binaryTriality_fixes_omega_span hi hH c hd (Or.inl hdegree) hz e⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
