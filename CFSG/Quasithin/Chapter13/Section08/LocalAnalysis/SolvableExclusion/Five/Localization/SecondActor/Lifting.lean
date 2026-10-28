module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data

/-!
# Lifting a starred factor within its original actor

For B* ≤ Vγ*, take the inverse image of B* inside Vγ, rather than the
whole inverse image in H. The resulting actual subgroup lies in Vγ and
has exactly B* as its image in H/O₂(H). This retains the subgroup needed
by the second-actor construction, including when Vγ meets O₂(H).

Source: Aschbacher–Smith, 13.8.13, printed p.951, construction of B₂.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor
variable {G : Type*} [Group G]

/-- Lift a starred subgroup inside the prescribed ambient actor, retaining
only those elements of that actor whose quotient image lies in the subgroup. -/
def liftWithin (H V : Subgroup G) (B : Subgroup (Source.Hstar H)) : Subgroup G :=
  ((V.subgroupOf H) ⊓ B.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem liftWithin_le (H V : Subgroup G) (B : Subgroup (Source.Hstar H)) :
    liftWithin H V B ≤ V := by
  rintro x ⟨v, hv, rfl⟩
  exact hv.1

theorem starImage_liftWithin (H V : Subgroup G) (B : Subgroup (Source.Hstar H))
    (hB : B ≤ Source.starImage H V) : Source.starImage H (liftWithin H V B) = B := by
  unfold Source.starImage liftWithin
  rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    exact hv.2
  · intro x hx
    obtain ⟨v, hv, he⟩ := hB hx
    refine ⟨v, ⟨hv, ?_⟩, he⟩
    change (QuotientGroup.mk' (pCore 2 H)) v ∈ B
    rwa [he]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor
