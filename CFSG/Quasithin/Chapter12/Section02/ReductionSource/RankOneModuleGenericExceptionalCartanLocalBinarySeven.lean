module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinarySeven
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original chosen input in the binary seven-centralizer

These applications retain the original T,L,V,H, both Hall subgroups and
containing component. The actual perfect residual of C_L(B) has the
original left two-core quotient and full omega-span action. The literal
kernel U ∩ O₂(CT) generates U under this residual, whose order-five
subgroup centralizes B and escapes CT. The binary exclusion and final
exceptional-component witness remain with the local Cartan proof.

Source: Aschbacher--Smith 5.1.10--13 and 12.2.2, printed pp.634--638,795,
with the seven-centralizer argument on pp.648--649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The actual seven-centralizer residual realizes the original left action. -/
theorem rankOne_local_cartan_binary_triality_seven_residual
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
    let D := L ⊓ centralizer (B : Set G)
    let R := residual D
    R ≤ D ∧ Group.IsPerfect R ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      (R.subgroupOf D).IsCComponent ∧
      (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ normalizer (R : Set G) ∧
      ∃ hRL : R ≤ L, ∃ e : (R ⧸ pCore 2 R) ≃* (L ⧸ pCore 2 L),
        (∀ x : R, e (QuotientGroup.mk' (pCore 2 R) x) =
          QuotientGroup.mk' (pCore 2 L) (inclusion hRL x)) ∧
        U = conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) R ∧
        (∀ V : Subgroup G, V ≤ U → conjugateSpanBy V L = conjugateSpanBy V R) :=
  BinaryOmega.original_binary_triality_seven_residual
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- The same core intersection generates the full original omega-span. -/
theorem rankOne_local_cartan_binary_triality_kernel_span
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
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let R := residual (L ⊓ centralizer (B : Set G))
    let E := U ⊓ X.pCoreIn 2
    omegaOneCenterAmbient (T : Subgroup G) ≤ E ∧
      conjugateSpanBy E R = U ∧
      (R ≤ normalizer (E : Set G) ↔ U ≤ X.pCoreIn 2) :=
  BinaryOmega.original_binary_triality_kernel_span
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- An actual quintic in the perfect seven-centralizer escapes the original CT. -/
theorem rankOne_local_cartan_binary_triality_seven_quintic_escape
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
    let R := residual (L ⊓ centralizer (B : Set G))
    ∃ F : Subgroup G, F ≤ R ∧ Nat.card F = 5 ∧
      F ≤ centralizer (B : Set G) ∧ ¬ F ≤ X :=
  BinaryOmega.original_binary_triality_seven_quintic_escape
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
