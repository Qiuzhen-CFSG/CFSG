module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNormalJanko
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original chosen module and the normal J₁ seven-subgroup

Apply the source normal-container sieve to the literal chosen-module input.
In its normal J₁ branch the original right Hall subgroup is cubic, the
original left degree is divisible by three, and A∩C is the order-seven
commutator [A∩Y,B], moved by B. Both Hall conditions, original quotients,
full Sylow choice and all earlier component exclusions are preserved.
Omega movement and the normal J₁ exclusion remain source obligations.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.637,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The full original sieve with its concrete normal J₁ seven-subgroup. -/
theorem rankOne_local_cartan_escape_seed_normalJanko_reduction
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
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) →
          Nat.card B = 3 ∧ 3 ∣ n ∧
          ⁅A ⊓ Y,B⁆ = A ⊓ C.map Y.subtype ∧ Nat.card (⁅A ⊓ Y,B⁆ : Subgroup G) = 7 ∧
          ⁅⁅A ⊓ Y,B⁆,B⁆ = ⁅A ⊓ Y,B⁆ ∧
          ¬ B ≤ centralizer ((⁅A ⊓ Y,B⁆ : Subgroup G) : Set G)) :=
  localCartan_escape_seed_normalJanko_reduction
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
