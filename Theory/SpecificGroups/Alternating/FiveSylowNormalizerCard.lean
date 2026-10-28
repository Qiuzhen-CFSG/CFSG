module

public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# Orders of Sylow two-normalizers in A₅

The five-point description identifies each Sylow two-normalizer with a point
stabilizer, of order twelve. Transport along a prescribed group equivalence
therefore excludes a factor of five from the same normalizer in any model.

Source application: Aschbacher--Smith 14.6.15, printed p.1035, in the
contained-component comparison with C.2.7(3).
-/

public section
namespace Theory.SpecificGroups.Alternating.FiveBorelOvergroups
open Subgroup

/-- A Sylow two-normalizer in A₅ has order twelve. -/
theorem sylow_normalizer_card (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (normalizer (P : Set (alternatingGroup (Fin 5)))) = 12 := by
  obtain ⟨i, hi⟩ := sylow_normalizer_eq_stabilizer P
  rw [hi, Nat.card_eq_fintype_card]
  clear P hi
  revert i
  decide +kernel

/-- This retains the specified equivalence and the original Sylow subgroup. -/
theorem sylow_normalizer_not_five_of_alternating_five
    {D : Type*} [Group D] [Finite D]
    (e : D ≃* alternatingGroup (Fin 5)) (P : Sylow 2 D) :
    ¬5 ∣ Nat.card (normalizer (P : Set D)) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (normalizer (P : Set D)).map e.toMonoidHom = normalizer (Q : Set _) :=
    map_normalizer_eq_of_bijective _ e.bijective
  have hc := sylow_normalizer_card Q
  rw [← he, card_map_of_injective e.injective] at hc
  rw [hc]
  decide

end Theory.SpecificGroups.Alternating.FiveBorelOvergroups
