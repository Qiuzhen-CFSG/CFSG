module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.Reflection

/-!
# The cubic partner of the original Tits first parabolic

Under the original Chapter 14 source hypotheses and a first-endpoint
isomorphism, the actual cubic subgroup is isomorphic to the second Tits
parabolic. The center census identifies its core inside the original common
Sylow. The computed marked outer quotient aligns its genuine conjugation
action; lifting through the central kernel gives the reflection equations,
which recognize the whole original endpoint.

The first-endpoint hypothesis is discharged by the marked quintic enumeration
owner. There are no additional core, action, quotient or reflection premises.
Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21, pp.988--989.
-/

public section
noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]

/-- The original second endpoint, with only the stipulated first-endpoint premise. -/
theorem source_second_parabolic
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
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    Nonempty (second ≃* (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) := by
  obtain ⟨σ,hcore⟩ := source_core_identification hG T hempty hM hu hmany
    hcard e H hH hi hfirst
  exact source_second_of_identified_core hG T hempty hM hu hmany
    hcard e H hH hi hfirst σ hcore

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
