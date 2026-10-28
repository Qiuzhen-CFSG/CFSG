module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalFiniteCarriers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalQuadratic

/-!
# Finite Cartan containing carriers for the chosen module

The original Chapter12 hypotheses supply the same whole reduced module.
The derived residual model excludes PSL₄(2), PSL₅(2), A₈ and M₁₁;
solvability of proper full-Sylow overgroups excludes M₁₂. The literal
same-container application retains the original quotient maps, both Hall
conditions, the full binary-triality endpoint and the A.3.6 alternatives.
Source: Aschbacher--Smith 5.1.12--13 and 12.2.2, printed
pp.635--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The five finite containing carriers are impossible for the original
chosen input, without an assumed residual quotient model. -/
theorem rankOne_local_cartan_not_finite_carriers
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype) :
    ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 4 2 ∨
      ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 5 2 ∨ IsAlternating (C ⧸ pCore 2 C) 8) ∧
    ¬ (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M11) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M12)) := by
  have hi := a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  refine ⟨LocalSieve.not_higher_binary_or_eight_container hi hH hgen hKL hKT horbit
    hY hescape C hC hKC, ?_⟩
  rintro (hm | hm)
  · exact LocalSieve.not_mathieu_eleven_container hi hH hgen hKL hKT horbit hY hescape C hC hKC hm
  · exact LocalSieve.not_mathieu_twelve_container hi.qtke
      (by rw [←hKT]; exact le_sup_left) hH.1.1.2 hKL horbit hY hescape C hC hKC hm

/-- The same-container source reduction also removing the five finite carriers. -/
theorem rankOne_local_cartan_finiteCarriers_reduction
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
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
          localBorel T L ≤ omegaCentralizer T ∧
          IsOneOrTwoA5Modules L (layer L (RankOneModule.wholeReduced T L)) ∧ Nat.card B = 7 ∧
          B ≤ centralizer
            (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23) →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3) ∧
        (∀ p e : ℕ, p.Prime → Odd p → (e = 1 ∨ e = 2) →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (p ^ e)) ∧
        ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 4 2 ∨
          ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 5 2 ∨ IsAlternating (C ⧸ pCore 2 C) 8) ∧
        ¬ (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M11) ∨
          Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M12)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        Chapter1.Section02.A36Common I ∧
          ((IsSimpleGroup I ∧ TheoremCModel I) ∨
            Chapter1.Section02.A36Natural I ∨ Chapter1.Section02.A36Nilpotent I) := by
  exact localCartan_escape_seed_finiteCarriers_reduction
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
