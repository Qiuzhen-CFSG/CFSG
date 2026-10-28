module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryOmega
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Original binary-triality omega-centralization at the chosen-module consumer

The ambient Baumann bound and genuine B.5.1 actor classification force the
same containing component and original H to centralize omega. The original
whole module has trivial fixed space and cannot be any sum of natural modules.
Escape persists in the actual omega centralizer. The original cubic, inverter,
both Hall conditions, quotient maps and all earlier exclusions are retained.
The binary branch itself and the other remaining local rows are still open.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.635--638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Apply ambient omega-centralization and the natural-row exclusions to the
original chosen module while retaining all earlier containing-component data. -/
theorem rankOne_local_cartan_escape_seed_binaryOmega_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          Even n ∧
          3 ∣ Nat.card ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) ∧
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          BinaryArmsPlacement T H Y C ∧ BinaryArmsAction T H A B Y C ∧
          BinaryCentralPlacement T H A Y C ∧
          C.map Y.subtype ≤ omegaCentralizer T ∧ H ≤ omegaCentralizer T ∧
          RankOneModule.wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ ∧
          (∀ (F : ChapterB.QuasisimpleSource.BinaryField) (k : ℕ),
            (¬ IsConjugationModel L (RankOneModule.wholeReduced T L) (ChapterB.QuasisimpleSource.repeated
              (ChapterB.QuasisimpleSource.linearNatural F 2) k)) ∧
            (¬ IsConjugationModel L (layer L (RankOneModule.wholeReduced T L)) (ChapterB.QuasisimpleSource.repeated
              (ChapterB.QuasisimpleSource.linearNatural F 2) k))) ∧
          omegaCentralizer T ∈ Chapter1.HOver G (H : Set G) ∧
          ¬ A ⊓ omegaCentralizer T ≤ normalizer (residual H : Set G) ∧
          ∃ D : Subgroup G, D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
            ¬ D ≤ normalizer (residual H : Set G) ∧
            ∃ t ∈ (T : Subgroup G) ⊓ C.map Y.subtype, t ∉ L ∧
              ∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))) :=
  localCartan_escape_seed_binaryOmega_reduction
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
