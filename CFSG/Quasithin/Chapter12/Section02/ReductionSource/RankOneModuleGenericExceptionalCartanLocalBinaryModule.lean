module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryModule
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original binary-triality minus torus at the chosen-module consumer

Apply the exhaustive constituent argument to the literal whole reduced
subgroup. In binary triality the original left degree is two modulo four.
The same original escaping cubic lies in the minus torus, which fixes an
actual nonidentity omega-point, and the same original inverter inverts
that torus modulo the original Sylow. No module marking, constituent
invariance, splitting, or change of field degree is assumed.

The remaining ambient placement and exclusion of the binary row, the
other containing rows, and the complete Cartan sieve remain open.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.635--638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- Use the literal wholeReduced input in the original binary-triality
branch, preserving the selected residual seed and containing component. -/
theorem rankOne_local_cartan_binary_inverted_minus_torus
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
    n % 4 = 2 ∧
      ∃ (D E : Subgroup G) (t z : G),
        D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
        ¬ D ≤ normalizer (residual H : Set G) ∧
        t ∈ (T : Subgroup G) ⊓ C.map Y.subtype ∧ t ∉ L ∧
        (∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
        (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1)=1) ∧
        z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
        E ≤ centralizer ({z} : Set G) ∧
        ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G) :=
  BinaryOmega.original_inverted_minus_torus
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
