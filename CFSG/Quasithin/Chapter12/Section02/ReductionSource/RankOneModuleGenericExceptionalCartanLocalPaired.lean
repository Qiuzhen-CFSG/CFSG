module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPaired
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Paired Cartan exclusion on the original Chapter 12 module

Apply the universal Hall-plane obstruction to wholeReduced. A literal
escaping cubic identifies the whole residual as a local C-component and
constructs its proper normal container in Y. At field degree two the
original left Cartan is already cubic. No invariant chosen submodule,
module coordinates or later recognition is used.

The same original input constructs the containing component alternatives:
normality, or the paired J₁/exceptional odd-prime PSL₂ rows with B = E₉.

Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.636–638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original whole reduced module supplies the source Input for cubic escape. -/
theorem rankOne_local_cartan_cubic_escape_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hCA : C ≤ A) (hCc : Nat.card C = 3)
    (hC : ¬ C ≤ normalizer (residual H : Set G)) :
    ((residual H).subgroupOf H).IsCComponent ∧
      IsQuasisimple (residual H ⧸ pCore 2 (residual H)) ∧
      residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X :=
  localCartan_cubic_escape_residual_component
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hpar c hY hescape hCA hCc hC

/-- With the original degree two, the paired case is excluded without an extra witness. -/
theorem rankOne_local_cartan_degree_two_escape_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ((residual H).subgroupOf H).IsCComponent ∧
      IsQuasisimple (residual H ⧸ pCore 2 (residual H)) ∧
      residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X :=
  localCartan_degree_two_escape_residual_component
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide : 1 < 2) hpsl)
    hH hpar c hY hescape

/-- The paired containing-model reduction uses the actual wholeReduced source Input. -/
theorem rankOne_local_cartan_containing_component_cases
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          (Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∨
            ∃ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p ∧
              ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p ∧
              Chapter1.Section02.LocalModels.IsAlternating
                ((K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 5))) :=
  localCartan_containing_component_cases
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hpar c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
