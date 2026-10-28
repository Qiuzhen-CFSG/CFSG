module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.CoreAction
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OuterQuotient


/-!
# Exact source action orders and conditional alignment through the outer quotient

The center calculation for the literal second Tits core gives center order
four and action-image order 1536 on the original source core under its given
marking. The original source hypotheses, σ and the marked core equality are
unchanged. The alignment theorem applies the outer-quotient reduction to this
same action, preserving its central kernel.

The marked outer quotient and order-six subgroup census are now proved on the
literal core. `source_core_action_alignment` applies the resulting full census
to the original conjugation image. The earlier conditional API is preserved.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--264, and14.2.20--21,
printed pp.988--989.
-/

@[expose] public section

noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G]

/-- The exact orders of the original core center and its actual action image. -/
theorem source_core_action_orders
    [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T (sourceResidual M Mc ⊔ (T : Subgroup G))
      le_sup_right σ = SecondRecognition.coreInSylow) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nat.card (center (pCore 2 X)) = 4 ∧
      Nat.card (markedCoreAction T X le_sup_right σ hcore).range = 1536 := by
  obtain ⟨_,_,_,hc⟩ := source_core_action_input hG T hempty hM hu hmany
    hcard e H hH hi hfirst σ hcore
  refine ⟨?_,?_⟩
  · exact (Nat.card_congr (centerCongr
      (markedCoreEquiv T _ le_sup_right σ hcore)).toEquiv).symm.trans
        SecondCoreAction.center_card
  · rw [SecondCoreAction.center_card] at hc
    omega

/-- The original source action aligns once the marked outer quotient and
its finite order-six subgroup calculation are supplied. These two independent
mathematical premises are not assertions of source amalgam recognition. -/
theorem source_core_action_alignment_of_outer_quotient
    [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T (sourceResidual M Mc ⊔ (T : Subgroup G))
      le_sup_right σ = SecondRecognition.coreInSylow)
    (q : MulAut SecondCoreAction.Core →* SecondCoreAction.OuterModel)
    (hq : Function.Surjective q)
    (hk : q.ker = MulAut.innerSubgroup SecondCoreAction.Core)
    (v : SecondCoreAction.BinaryPair)
    (hv : SecondCoreAction.markedTransposition v ∈ SecondCoreAction.sylow.range.map q)
    (hsmall : ∀ (w : SecondCoreAction.BinaryPair)
      (U V : Subgroup SecondCoreAction.OuterModel),
      SecondCoreAction.markedTransposition w ∈ U →
      SecondCoreAction.markedTransposition w ∈ V →
      Nat.card U = 6 → Nat.card V = 6 →
      ∃ b : SecondCoreAction.OuterModel, U.map (MulAut.conj b).toMonoidHom = V) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ∃ d : SecondCoreAction.Core ≃* pCore 2 X,
      (SecondCoreAction.through (pCore 2 X) d).range = SecondCoreAction.model.range ∧
      (SecondCoreAction.through (pCore 2 X) d).ker =
        (center (pCore 2 X)).map (pCore 2 X).subtype := by
  exact source_core_action_alignment_of_census hG T hempty hM hu hmany
    hcard e H hH hi hfirst σ hcore
    (SecondCoreAction.action_census_of_marked_outer_quotient q hq hk v hv hsmall)

/-- Conjugacy of the actual source core action, with the finite census discharged. -/
theorem source_core_action_alignment
    [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T (sourceResidual M Mc ⊔ (T : Subgroup G))
      le_sup_right σ = SecondRecognition.coreInSylow) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ∃ d : SecondCoreAction.Core ≃* pCore 2 X,
      (SecondCoreAction.through (pCore 2 X) d).range = SecondCoreAction.model.range ∧
      (SecondCoreAction.through (pCore 2 X) d).ker =
        (center (pCore 2 X)).map (pCore 2 X).subtype := by
  exact source_core_action_alignment_of_census hG T hempty hM hu hmany
    hcard e H hH hi hfirst σ hcore SecondCoreAction.action_census

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
