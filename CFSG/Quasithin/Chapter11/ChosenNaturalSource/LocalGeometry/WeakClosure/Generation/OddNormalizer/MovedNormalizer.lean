module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedLocalGeometry
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The full normalizer of the moved residual in its central quotient

Uniqueness bounds N_G(F) using the nontrivial characteristic subgroup O₂(F).
Inside the actual component of N_G(A), the reverse inclusion follows from
the original fixed-residual definition. Perfectness reflects normalization
through the central quotient, so the full projected normalizer is the image
of the original intersection with N_G(L).

This supplies the precise local-normalizer premise in the moved J₄ branch
of Aschbacher--Smith 4.4.6--12, printed pp.620--622. No containment of a full
ambient Sylow subgroup is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The original residual has its whole ambient normalizer in N_G(L). -/
theorem moved_residual_normalizer_le {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    normalizer (oddActorResidual L A : Set G) ≤ normalizer (L : Set G) := by
  let F := oddActorResidual L A
  have hchar := normalizer_le_normalizer_characteristic_image F (pCore 2 F)
  have hn := normalizer_le_of_unique_maximalTwoLocal hu.2.2
    (isPGroup_pCoreIn 2 F) (actor_cover D S hA hodd).2.2.2
    (F.le_normalizer.trans hchar)
  exact hchar.trans hn

/-- Relative normality identifies the residual normalizer in the component. -/
theorem moved_component_residual_normalizer {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    normalizer (movedComponentSubgroup A (oddActorResidual L A) K : Set K) =
      movedComponentSubgroup A (normalizer (L : Set G)) K := by
  have hFK' : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤ K := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hFK hx
    exact (Subtype.ext he : k = x) ▸ hk
  rw [←subgroupOf_normalizer_eq hFK',
    ←subgroupOf_normalizer_eq (hFK.trans (map_subtype_le _))]
  ext k
  exact ⟨fun hk => moved_residual_normalizer_le D S hA hodd hu hk,
    fun hk => normalizes_oddActorResidual L A ⟨hk,k.val.property⟩⟩

/-- The normalizer after central projection is exactly the original intersection image. -/
theorem moved_projected_residual_normalizer {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    normalizer ((movedComponentSubgroup A (oddActorResidual L A) K).map
        (QuotientGroup.mk' (center K)) : Set (K ⧸ center K)) =
      (movedComponentSubgroup A (normalizer (L : Set G)) K).map
        (QuotientGroup.mk' (center K)) := by
  let Y := movedComponentSubgroup A (oddActorResidual L A) K
  have hFK' : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤ K := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hFK hx
    exact (Subtype.ext he : k = x) ▸ hk
  let a : Y ≃* oddActorResidual L A := (subgroupOfEquivOfLe hFK').trans
    (subgroupOfEquivOfLe (hFK.trans (map_subtype_le _)))
  let : Group.IsPerfect (oddActorResidual L A) := oddActorResidual_isPerfect L A
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  have he := comap_normalizer_map_eq_of_perfect (QuotientGroup.mk' (center K))
    (by rw [QuotientGroup.ker_mk']) Y
  rw [moved_component_residual_normalizer D S hA hodd hu K hFK] at he
  have hm := congrArg (map (QuotientGroup.mk' (center K))) he
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
  exact hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
