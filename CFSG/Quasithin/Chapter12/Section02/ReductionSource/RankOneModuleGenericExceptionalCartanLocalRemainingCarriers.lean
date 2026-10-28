module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRemainingCarriers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalFiniteCarriers

/-!
# Remaining Cartan carriers for the original chosen module

The original Chapter12 input supplies the whole reduced module to the
source classification. The HS and Rudvalis rows now have the literal
PSL₂(4) residual quotient and original cubic right Hall. The exhaustive
Theorem C reduction applies the completed A₇, J₂ and M₂₃ witnesses to
that same whole module; its other alternatives retain the same selected
component and the complete binary-triality endpoint. Four simple carriers
and both noncentral-Fitting rows remain explicit source obligations.
Source: Aschbacher–Smith 5.1.12–13 and 12.2.2, printed pp.635–638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- Both sparse sporadic rows give the original fixed seed, residual model
and right Hall order without additional section or action assumptions. -/
theorem rankOne_local_cartan_sparse_residual_and_hall
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model)) :
    K = residual H ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      Nat.card B = 3 := by
  exact LocalSieve.higmanSims_rudvalis_residual_and_hall
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKL hKT horbit hY hescape C hC hKC hm

/-- The full carrier catalogue, with every completed exceptional branch
applied to the original whole reduced module. -/
theorem rankOne_local_cartan_remaining_carriers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H) ∨
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        A36Common I ∧
          ((K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L (RankOneModule.wholeReduced T L)) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨
          (IsSimpleGroup I ∧
            (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M24) ∨
              Nonempty ((C ⧸ pCore 2 C) ≃* Held.He) ∨
              ((Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
                Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model)) ∧
                K = residual H ∧
                ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
                Nat.card B = 3))) ∨
          A36Natural I ∨ A36Nilpotent I) := by
  exact localCartan_escape_remaining_carriers
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
