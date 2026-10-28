module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original binary-triality torus in a point-centralizer component

Use the literal whole reduced subgroup in the point-component construction.
The same escaping cubic and inverter place the minus torus in a normal
C-component of its fixed omega-point centralizer. The original triality
component lies in this component, with its two-core quotient preserved on
the actual image. Either the original degree is two or the inclusion is
strict. The torus order survives the new component's full two-core quotient.

This does not yet exclude binary triality or establish the complete local
Cartan sieve. Source: Aschbacher--Smith 5.1.13 and 12.2.2,
printed pp.635--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- Place the same escaping cubic and minus torus in a genuine normal
component of the fixed point centralizer, using the literal wholeReduced input.
Higher original degree forces a strict enlargement of the triality component. -/
theorem rankOne_local_cartan_binary_minus_torus_point_component
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
      ∃ (D E J : Subgroup G) (t z : G),
        D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
        ¬ D ≤ normalizer (residual H : Set G) ∧
        t ∈ (T : Subgroup G) ⊓ C.map Y.subtype ∧ t ∉ L ∧
        (∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
        (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1)=1) ∧
        z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
        E ≤ centralizer ({z} : Set G) ∧
        (∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G)) ∧
        C.map Y.subtype ≤ J ∧ residual H ≤ J ∧ J ≤ centralizer ({z} : Set G) ∧
        (J.subgroupOf (centralizer ({z} : Set G))).IsCComponent ∧
        (J.subgroupOf (centralizer ({z} : Set G))).Normal ∧
        J ∈ Chapter1.L G (T : Subgroup G) ∧ E ≤ J ∧
        Nat.card ((E.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 2^(n/2)+1 ∧
        Nonempty ((C ⧸ pCore 2 C) ≃*
          (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ⧸
            pCore 2 (((C.map Y.subtype).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))))) ∧
        (n = 2 ∨ C.map Y.subtype < J) ∧
        centralizer ({z} : Set G) ∈ Chapter1.HOver G (H : Set G) ∧
        ¬ A ⊓ centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) :=
  BinaryOmega.original_minus_torus_point_component
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
