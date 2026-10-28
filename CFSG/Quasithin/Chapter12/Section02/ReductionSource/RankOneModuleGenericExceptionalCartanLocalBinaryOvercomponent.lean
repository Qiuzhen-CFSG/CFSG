module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryOvercomponent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original binary-triality point-component restrictions in Chapter 12

Apply the new containing-component restrictions to the literal wholeReduced
input. The point component has a quasisimple two-core quotient containing
the original triality section. Its checked order excludes all sporadic
carriers, J₁, small alternating groups and the binary linear entries.
A strict enlargement also excludes every rank-two characteristic-two model.
The same cubic, minus torus, inverter, point and original residual survive.

The original degree-two binary case and the other containing rows remain
open. Source: Aschbacher--Smith 5.1.13 and 12.2.2,
printed pp.635--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- Restrict the same point component with the original wholeReduced input,
retaining the full torus and quotient-section data. -/
theorem rankOne_local_cartan_binary_point_component_restrictions
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
        (n = 2 ∨ (C.map Y.subtype < J ∧
          ¬ RankTwoTheoremC (J ⧸ pCore 2 J))) ∧
        centralizer ({z} : Set G) ∈ Chapter1.HOver G (H : Set G) ∧
        ¬ A ⊓ centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧
        211341312 ∣ Nat.card (J ⧸ pCore 2 J) ∧
        ¬ (ClassificationModels.IsSporadicModel (J ⧸ pCore 2 J) ∨
          Nonempty ((J ⧸ pCore 2 J) ≃* Janko1.Model)) ∧
        (∀ d : ℕ, 5 ≤ d → d ≤ 8 → ¬ IsAlternating (J ⧸ pCore 2 J) d) ∧
        (∀ d : ℕ, d = 4 ∨ d = 5 → ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) :=
  BinaryOmega.original_minus_torus_point_component_restrictions
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
