module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.ActionAlignment
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.CoreIdentification
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.ReflectionFromAction
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OrderSixApplication

/-!
# Original cubic reflection from the marked outer quotient

The index-two census identifies the actual core inside the original Sylow.
The order-six subgroup theorem aligns its conjugation image, and the
central-kernel lifting theorem reconstructs the reflection on that same Sylow.
The checked collection equations then identify the original cubic endpoint.

The marked outer quotient of the actual core automorphism group is now
constructed. `source_reflection` and `source_second_of_identified_core`
discharge that input and retain the exact original marked core. Earlier
conditional interfaces are preserved for existing consumers.
Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21, pp.988--989.
-/

public section
noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]

/-- The actual source action aligns using the proved core and order-six
censuses. Only the marked outer quotient remains to be constructed. -/
theorem source_core_action_of_marked_outer_quotient
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
    (q : MulAut SecondCoreAction.Core →* SecondCoreAction.OuterModel)
    (hq : Function.Surjective q)
    (hk : q.ker = MulAut.innerSubgroup SecondCoreAction.Core)
    (v : SecondCoreAction.BinaryPair)
    (hv : SecondCoreAction.markedTransposition v ∈ SecondCoreAction.sylow.range.map q) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ∃ d : SecondCoreAction.Core ≃* pCore 2 X,
      (SecondCoreAction.through (pCore 2 X) d).range = SecondCoreAction.model.range ∧
      (SecondCoreAction.through (pCore 2 X) d).ker =
        (center (pCore 2 X)).map (pCore 2 X).subtype := by
  obtain ⟨σ,hcore⟩ := source_core_identification hG T hempty hM hu hmany
    hcard e H hH hi hfirst
  exact source_core_action_alignment_of_census hG T hempty hM hu hmany
    hcard e H hH hi hfirst σ hcore
    (SecondCoreAction.action_census_of_outer_quotient q hq hk v hv)

/-- Construct the literal three-coset reflection equations on the original
Sylow, conditional only on the marked quotient of the model core. -/
theorem source_reflection_of_marked_outer_quotient
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
    (q : MulAut SecondCoreAction.Core →* SecondCoreAction.OuterModel)
    (hq : Function.Surjective q)
    (hk : q.ker = MulAut.innerSubgroup SecondCoreAction.Core)
    (v : SecondCoreAction.BinaryPair)
    (hv : SecondCoreAction.markedTransposition v ∈ SecondCoreAction.sylow.range.map q) :
    ∃ (τ : S ≃* (T : Subgroup G))
      (r : (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)),
      (r : G) ∉ (T : Subgroup G) ∧
      Tits.AmalgamRigidity.SecondExtension.CosetRelations
        (SecondRecognition.generators
          (sylowMap T (sourceResidual M Mc ⊔ (T : Subgroup G)) le_sup_right τ) r) := by
  obtain ⟨d,himage,_⟩ := source_core_action_of_marked_outer_quotient
    hG T hempty hM hu hmany hcard e H hH hi hfirst q hq hk v hv
  exact source_reflection_of_core_action hG T hempty hM hu hmany
    hcard e H hH hi hfirst SecondCoreAction.center_card
    SecondCoreAction.centralizer_center d himage

/-- The original cubic endpoint is the actual second Tits parabolic once its
marked core outer quotient is supplied. The first-endpoint premise is unchanged. -/
theorem source_second_of_marked_outer_quotient
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
    (q : MulAut SecondCoreAction.Core →* SecondCoreAction.OuterModel)
    (hq : Function.Surjective q)
    (hk : q.ker = MulAut.innerSubgroup SecondCoreAction.Core)
    (v : SecondCoreAction.BinaryPair)
    (hv : SecondCoreAction.markedTransposition v ∈ SecondCoreAction.sylow.range.map q) :
    Nonempty (second ≃* (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) := by
  obtain ⟨τ,r,hr,htable⟩ := source_reflection_of_marked_outer_quotient
    hG T hempty hM hu hmany hcard e H hH hi hfirst q hq hk v hv
  exact source_second_of_collection hG T hempty hM hu hmany hcard e H hH hi hfirst
    τ r hr htable

/-- The literal cubic reflection on the same original Sylow, with all model inputs proved. -/
theorem source_reflection
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
    ∃ (τ : S ≃* (T : Subgroup G))
      (r : (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)),
      (r : G) ∉ (T : Subgroup G) ∧
      Tits.AmalgamRigidity.SecondExtension.CosetRelations
        (SecondRecognition.generators
          (sylowMap T (sourceResidual M Mc ⊔ (T : Subgroup G)) le_sup_right τ) r) := by
  obtain ⟨d,himage,_⟩ := source_core_action_alignment
    hG T hempty hM hu hmany hcard e H hH hi hfirst σ hcore
  exact source_reflection_of_core_action hG T hempty hM hu hmany
    hcard e H hH hi hfirst SecondCoreAction.center_card
    SecondCoreAction.centralizer_center d himage


/-- Recognition from the identified original core, with no action or quotient callback. -/
theorem source_second_of_identified_core
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
    Nonempty (second ≃* (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) := by
  obtain ⟨τ,r,hr,htable⟩ := source_reflection
    hG T hempty hM hu hmany hcard e H hH hi hfirst σ hcore
  exact source_second_of_collection hG T hempty hM hu hmany hcard e H hH hi hfirst
    τ r hr htable

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
