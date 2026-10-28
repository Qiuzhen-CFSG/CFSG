module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCoreDisplacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Core displacement for the original chosen-module input

The original chosen input supplies the exact Borel stabilizer of every
nontrivial characteristic subgroup of O₂(CT). A single quintic in the
perfect seven-centralizer moves all of them and generates L join CT,
whose two-core is trivial. Both Hall conditions, the original residual,
the containing component and the actual core are retained.

This is the chosen-module application of the core configuration in the
local Cartan sieve, not its binary-triality exclusion or final witness.
Source: Aschbacher--Smith 5.1.10--13 and 12.2.2, pp.634--638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The original Borel is the exact stabilizer in L of the retained core and its nontrivial characteristic subgroups. -/
theorem rankOne_local_cartan_binary_triality_core_stabilizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let Q := X.pCoreIn 2
    L ⊓ normalizer (Q : Set G) = localBorel T L ∧
      ∀ D : Subgroup Q, D.Characteristic → D ≠ ⊥ →
        L ⊓ normalizer (D.map Q.subtype : Set G) = localBorel T L :=
  BinaryOmega.original_binary_triality_core_stabilizers
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- The original seven-centralizer supplies a single quintic moving every nontrivial characteristic subgroup of the retained core. -/
theorem rankOne_local_cartan_binary_triality_quintic_core_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let Q := X.pCoreIn 2
    let R := residual (L ⊓ centralizer (B : Set G))
    ∃ F : Subgroup G, F ≤ R ∧ Nat.card F = 5 ∧ F ≤ centralizer (B : Set G) ∧
      F ⊔ X = L ⊔ X ∧ (F ⊔ X).pCoreIn 2 = ⊥ ∧
      ¬ F ≤ normalizer (Q : Set G) ∧
      (∀ D : Subgroup Q, D.Characteristic → D ≠ ⊥ →
        ¬ F ≤ normalizer (D.map Q.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsPGroup 2 N → N ≠ ⊥ →
        X ≤ normalizer (N : Set G) → ¬ F ≤ normalizer (N : Set G)) :=
  BinaryOmega.original_binary_triality_quintic_core_displacement
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
