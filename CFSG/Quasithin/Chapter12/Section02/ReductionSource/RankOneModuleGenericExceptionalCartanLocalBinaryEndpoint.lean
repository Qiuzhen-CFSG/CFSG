module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryEndpoint
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The binary-triality endpoint on the original chosen module

The wholeReduced input identifies the entire moved layer as one or two
A₅ modules. Restriction gives an actual conjugation model on the original
chosen subgroup. The same right Hall subgroup has order seven, fixes the
noncentral omega-span of order at least sixteen, and its centralizer covers
the original L/O₂(L) through inclusion. The original sieve applies these
facts to its selected component while retaining all previous exclusions.

The containing quotient is still binary triality and the right residual
quotient is PSL₂(8); this is not an exceptional-component witness or a
completion of the local Cartan escape. Both Hall conditions, the original
Sylow and every literal quotient are retained.

Source: Aschbacher--Smith 5.1.10--13 and 12.2.2,
printed pp.634--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The original chosen subgroup has its actual A₅ conjugation model in
the triality row; the original right Hall subgroup is the seven-actor. -/
theorem rankOne_local_cartan_binary_triality_module_and_hall
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
    n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
      localBorel T L ≤ omegaCentralizer T ∧
      IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L) ∧
      IsConjugationModel L V a5Module ∧ Nat.card B = 7 ∧
      B ≤ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  obtain ⟨hn,ha,hAC,hBorel,hmodule,hb,hfix⟩ :=
    BinaryOmega.original_binary_triality_module_and_hall
      (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
      hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  exact ⟨hn,ha,hAC,hBorel,hmodule,
    a.a5_model_of_one_or_two_on_overgroup a.le_rankOne_commutatorLayer hmodule,hb,hfix⟩

/-- The chosen input constructs the noncentral omega-span fixed by the
same seven-group and the literal quotient-covering seven-centralizer. -/
theorem rankOne_local_cartan_binary_triality_fixed_omega_span
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
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    Input KnownSimple.IsKnownSimple T L U 2 ∧
      16 ≤ Nat.card U ∧ Nat.card B = 7 ∧ B ≤ centralizer (U : Set G) ∧
      ∃ e : ((L ⊓ centralizer (B : Set G) : Subgroup G) ⧸
          pCore 2 (L ⊓ centralizer (B : Set G) : Subgroup G)) ≃* (L ⧸ pCore 2 L),
        ∀ x : (L ⊓ centralizer (B : Set G) : Subgroup G),
          e (QuotientGroup.mk' (pCore 2 (L ⊓ centralizer (B : Set G) : Subgroup G)) x) =
            QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left x) :=
  BinaryOmega.original_binary_triality_fixed_omega_span
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm


open Chapter1.Section02.LocalModels
/-- The original chosen-module sieve retains its component witnesses,
all previous exclusions and the binary endpoint on its whole reduced layer. -/
theorem rankOne_local_cartan_seed_binary_endpoint_reduction
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
          IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L) ∧ Nat.card B = 7 ∧
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
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) := by
  exact localCartan_escape_seed_binary_endpoint_reduction
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
