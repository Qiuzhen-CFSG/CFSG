module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Index

/-!
# Order of the actual even G₂ outer quotient

Inner-field coverage makes the coefficient-field automorphisms surject onto
the quotient by inner automorphisms. The outer order therefore divides the
field automorphism order. This supplies the outer factor in the natural
automizer bound in Aschbacher--Smith 11.2.1, printed pp.766--767.
-/

public section
namespace Atlas.G2.LieAutomorphismExtensions
open Subgroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Field automorphisms cover the actual quotient by inner automorphisms. -/
theorem outer_card_dvd_fieldAut (hq : 2 < Nat.card F) :
    Nat.card (MulAut.Outer (Model F)) ∣ Nat.card (F ≃+* F) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Model F))
  let f := q.comp (fieldAction (F := F))
  apply card_dvd_of_surjective f
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨g,σ,rfl⟩ := exists_inner_field hq a
  refine ⟨σ, ?_⟩
  change q _ = q (_ * _)
  rw [map_mul, show q (MulAut.conj g) = 1 from
    (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩, one_mul]

end Atlas.G2.LieAutomorphismExtensions
