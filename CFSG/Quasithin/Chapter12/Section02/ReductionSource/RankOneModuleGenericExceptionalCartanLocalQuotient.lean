module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Literal local quotient actions on the original Chapter 12 module

Instantiate the universal generic input on the whole reduced subgroup.
The moved seed gives an actual A₅ × A₅ residual quotient. Independently,
the containing component's normal Sylow orbit carries the original
Cartan quotient action: its cyclic odd image is normalized by the right
Hall image and still fails to normalize the residual image.

These are the quotient and action reductions of the local sieve. The
remaining containing-model exclusions, escaping cubic, A₇ contradiction
and whole-module recognition stay with the local classification owner.
Source: Aschbacher--Smith 5.1.10--13 and 12.2.2, pp.634--638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original whole reduced module supplies the actual residual quotient alternative. -/
theorem rankOne_local_cartan_residual_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) ∨
      (IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∧
        residual H ∈ Chapter1.L G (T : Subgroup G) ∧
        ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
          (X.subgroupOf Y).Normal ∧ residual H < X) :=
  localCartan_escape_residual_quotient
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

/-- The original Cartan escapes on the literal normal component-orbit quotient. -/
theorem rankOne_local_cartan_escaping_component_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ C : Subgroup Y, C.IsCComponent ∧
      residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
      ∃ hn : ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal,
        let J := (componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y
        letI : J.Normal := hn
        let f := normalQuotientAction J (pCore 2 J)
        let Dbar := (A.subgroupOf Y).map f
        let Bbar := (B.subgroupOf Y).map f
        IsCyclic Dbar ∧ Odd (Nat.card Dbar) ∧
          Bbar ≤ normalizer (Dbar : Set (MulAut (J ⧸ pCore 2 J))) ∧
          ¬ Dbar ≤ normalizer (((residual H).subgroupOf Y).map f : Set _) ∧
          Dbar ≠ ⊥ ∧ ¬ Dbar ≤ Bbar :=
  localCartan_exists_escaping_component_action
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
