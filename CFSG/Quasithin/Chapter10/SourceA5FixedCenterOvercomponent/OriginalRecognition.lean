module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.PositiveCenterOddCore
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.LayerKernel
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SmallChiefSource

/-!
# Recognition of the original positive-center head from its local shortlist

The original central-four geometry kills the odd core of the actual
second-vector centralizer. The resulting exact action kernel identifies
I/O₂(I) with the faithful small-chief actor, which the literal shortlist
forces to be A₇. Thus no odd central cover is silently removed from the
source classification. The local shortlist remains an explicit input.

Source: Aschbacher–Smith 10.2.1, printed p.743, using A.3.14 and B.4.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal shortlist forces the actual head to be A₇, since the
positive-center geometry removes the central kernel of its faithful action. -/
theorem source_a5_original_overcomponent_seven_of_shortlist
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (p : SourceA5OriginalFixedPair D t) {I : Subgroup G} (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({p.second} : Set G))
    (hI : (I.subgroupOf (centralizer ({p.second} : Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (centralizer ({p.second} : Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hhead : IsQuasisimple (I ⧸ pCore 2 I))
    (hlist : let H := I ⧸ pCore 2 I
      IsAlternating H 7 ∨ IsAlternatingCover H 7 ∨ Nonempty (H ≃* Janko1.Model) ∨
      ClassicalGroup.IsPSL H 2 25 ∨ ∃ r, A312ExceptionalPrime r ∧ ClassicalGroup.IsPSL H 2 r) :
    Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  have ho := source_a5_original_second_centralizer_oddCore_eq_bot D e hn hout ht htn p
  have hk := source_a5_overcomponent_layer_centralizer_eq_core D e hn hout hLI hIX hI hS ho hU
  have hv : orderOf p.second = 2 := by
    let := D.module_elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ p.second_module)
      p.second_ne
  have ha := (source_a5_involution_overcomponent_head_and_actor_seven_of_shortlist
    D e hn hout hv hLI hIX hI hS hU hhead hlist).2
  obtain ⟨ea⟩ := ha
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans ea⟩

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
