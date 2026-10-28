module
public import CFSG.Quasithin.Chapter10.SourceNonnormalCoveringCounterexample
public import CFSG.Quasithin.Chapter10.SourceA5OddNormalizerCore
public import CFSG.Quasithin.Chapter10.SourceNonnormalOddActorOrbit
public import Theory.GroupTheory.TwoLocalCoreObstruction
/-!
# The literal odd-prime normalizer supplies the contrary C.2.8 configuration

For B centralizing both the full component quotient and the original module,
L_B=C_{L₀}(B)^∞ covers L₀ and contains the nonzero module in its two-core.
Thus I=L_B N_T(B) has a nontrivial two-core and lies in M∩N_G(B).
If B is an odd-prime subgroup permuting with T, its normalizer retains the
original component orbit. A nontrivial two-core in an escaping N_G(B) would
therefore produce the strict C.2.8 configuration whose individual component
is not normal in H∩M.

This is the actual-source input and two-core reduction in 4.4.6–7,
Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.620.
The source C.4.8 theorem must still exclude that contrary configuration;
this module does not assume its normality conclusion or assert Hall placement.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual fixed residual and N_T(B) satisfy the source cover and core clauses. -/
theorem source_oddActor_normalizerJoin_input
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G)) :
    let I := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))
    I ≤ D.maximalLocal ∧ I ≤ normalizer (B : Set G) ∧
      (localOrbit T L : Set G) ⊆ (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G) ∧
      I.pCoreIn 2 ≠ ⊥ := by
  let X := localOrbit T L
  let F := (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
    (X ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
  obtain ⟨hcover,_,hVF⟩ := source_fullModule_oddActor_cover D B hB hodd hBV
  change (X : Set G) = (F : Set G) * (X.pCoreIn 2 : Set G) at hcover
  change D.fullModule ≤ F.pCoreIn 2 at hVF
  have hIM : I ≤ D.maximalLocal := sup_le
    (((map_subtype_le (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_left).trans X.le_normalizer)
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hIN : I ≤ normalizer (B : Set G) := sup_le
    (((map_subtype_le (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
    inf_le_right
  have hVI : D.fullModule ≤ I := hVF.trans ((pCoreIn_le 2 F).trans le_sup_left)
  have hcore : D.fullModule ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 F).to_le hVF) hVI (hIM.trans D.maximalLocal_normalizes_fullModule)
  refine ⟨hIM,hIN,hcover.subset.trans
    (Set.mul_subset_mul (show F ≤ I from le_sup_left) Set.Subset.rfl),?_⟩
  intro he
  apply D.module_ne_bot
  exact bot_unique (((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans hcore).trans_eq he)

/-- An escaping odd-prime normalizer with a nontrivial two-core gives the literal C.4.8 contradiction target. -/
theorem source_oddPrimeNormalizer_twoCore_counterexample
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal)
    (hcore : pCore 2 (normalizer (B : Set G)) ≠ ⊥) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      H ⊓ D.maximalLocal < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ H ⊓ D.maximalLocal ≤ normalizer
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype : Set G) := by
  let X := localOrbit T L
  let F := (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
    (X ⊓ centralizer (B : Set G)).subtype
  let TB := (T : Subgroup G) ⊓ normalizer (B : Set G)
  let I := F ⊔ TB
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,hn⟩ := hB.exists_card_eq
    rw [hn]
    exact hp.pow
  obtain ⟨hIM,hIN,hcover,hIcore⟩ := source_oddActor_normalizerJoin_input D B hBC hodd hBV
  change I ≤ D.maximalLocal at hIM
  change I ≤ normalizer (B : Set G) at hIN
  have hTBo := source_oddPrimeActor_normalizer_orbit D hp B hB hBC hperm
  have hIo : componentOrbit L I = X := by
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer _ _ _ (le_componentOrbit L T) hIM
    · apply hTBo.symm.le.trans
      exact iSup_le fun t => le_iSup_of_le
        (⟨t,(show TB ≤ I from le_sup_right) t.property⟩ : I) le_rfl
  have hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal := by
    intro hu
    obtain ⟨N,hN,hBN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
      (normalizer (B : Set G)) hcore
    exact hout ((hu.2.2 N hN (hIN.trans hBN)) ▸ hBN)
  obtain ⟨J,H,S,_,_,_,hlt,hC28,hnorm⟩ :=
    source_covering_counterexample_C28 D hn hIM hcover hIcore hIo hnot
  exact ⟨J,H,S,hlt,hC28,hnorm⟩
end CFSG.Quasithin.Chapter10
