module

public import Theory.Representation.G2NaturalExtensions.FixedSpaces
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# Fixed lifting for central covers of the derived G₂ natural module

Every commutator-generated central cover of the genuine derived natural
module is a quotient of the trace-zero octonion module. Norm preservation
removes a scalar displacement of a trace-zero representative, so an element
fixing the natural image fixes the original vector. No extension of the
derived-group action to the full G₂ group is needed.

Source: Aschbacher–Smith, B.4.6(7) and I.2.3(1), printed pp.88,413.
-/

public section

open Representation Representation.OneCohomology

namespace Atlas.G2.Natural.Extensions

variable {F V : Type*} [Field F] [CharP F 2] [Finite F]
  [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Fixing a natural image in a central cover already fixes its original
vector, for the actual derived actor. -/
theorem derived_fixed_of_natural_fixed
    {σ : Representation (ZMod 2) (commutator (Model F)) V}
    (p : σ.IntertwiningMap (OrthogonalCover.binaryNatural F)) (hp : IsCover p)
    (g : commutator (Model F)) (v : V)
    (hv : derivedAction F g (p v) = p v) : σ g v = v := by
  obtain ⟨f, hf, hover⟩ := OrthogonalCover.exists_quotient F p hp
  obtain ⟨w, rfl⟩ := hf v
  have hw : traceZeroAction F g.val w = w := by
    apply traceZero_fixed_of_natural_fixed
    simpa only [derivedAction_apply, hover] using hv
  have he := IntertwiningMap.isIntertwining
    (OrthogonalCover.binaryAction F) σ f g w
  change f (traceZeroAction F g.val w) = σ g (f w) at he
  rw [hw] at he
  exact he.symm

end Atlas.G2.Natural.Extensions
