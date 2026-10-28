module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNoncentral
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalFiniteCarriers

/-!
# The nonquasisimple Cartan step for the literal chosen module

Both remaining nonquasisimple containing rows now construct the original
residual inside a smaller involution-centralizer residual. The original
cyclic actor and full Sylow normalize that subgroup, and the restriction
of the actual Fitting quotient map identifies it with prime-field SL₂.

This application retains the whole chosen module, both Hall conditions,
the same selected container, literal quotient images and all binary-triality
clauses. The companion NoncentralExclusion module excludes these two rows;
the binary ambient exclusion remains open.
Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.636,795,
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

/-- The literal chosen module constructs the smaller SL₂ residual in both
nonquasisimple rows, retaining the full original exceptional conclusion. -/
theorem rankOne_local_cartan_binary_or_noncentral_section
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
        A36Common I ∧ K = residual H ∧
          ((K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L (RankOneModule.wholeReduced T L)) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨
          ((A36Natural I ∨ A36Nilpotent I) ∧ NoncentralCartanSection T H A Y C)) := by
  exact localCartan_escape_binary_or_noncentral_section
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
