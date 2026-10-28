module

public import Stellmacher.ElementaryAbelianMaxJMap
import all Stellmacher.ElementaryAbelianMaxJMap

/-!
# Maximum elementary families under injective maps

This specification extension publishes the family transport already proved
internally for the elementary Thompson image theorem. The deliberate
`import all` keeps the implementation coupling inside the Stellmacher package;
clients use the public family statement without access to its private proof.
No shared foundational module is changed.

The source application is the internal-product identification in
Aschbacher--Smith, 16.3.12, printed p.1182.
-/

public section
namespace Stellmacher

/-- An injective map preserves and reflects the maximum elementary family. -/
public theorem maxFamily_map_injective_iff
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (S A : Subgroup G) :
    A.map f ∈ elementaryAbelianMaxSubgroups (S.map f) ↔
      A ∈ elementaryAbelianMaxSubgroups S :=
  maxFamily_map_iff f hf S A

open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- An isomorphism onto an ambient subgroup transports the entire family. -/
theorem maxFamily_equiv_iff (S : Subgroup G) (e : H ≃* S) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups S ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H),
        A = B.map (S.subtype.comp e.toMonoidHom) := by
  let f := S.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := S.subtype_injective.comp e.injective
  have hr : (⊤ : Subgroup H).map f = S := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact (e a).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, mem_top _, congrArg Subtype.val (e.apply_symm_apply _)⟩
  constructor
  · intro hA
    have hm : (A.comap f).map f = A := by
      apply map_comap_eq_self
      rw [MonoidHom.range_eq_map, hr]
      exact hA.1
    refine ⟨A.comap f, ?_, hm.symm⟩
    apply (maxFamily_map_injective_iff f hf ⊤ _).mp
    rwa [hr, hm]
  · rintro ⟨B, hB, rfl⟩
    have h := (maxFamily_map_injective_iff f hf ⊤ B).mpr hB
    rwa [hr] at h

end Stellmacher
