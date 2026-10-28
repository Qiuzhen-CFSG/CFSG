module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags
public import Theory.Representation.PSL3Two.ParabolicCyclic.Basic
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# The literal residual actor for parabolic chief counts

The embedded intrinsic two-residual is identified with the existing matrix
model `lineA`. Cubic elements of the parabolic lie in this residual, providing
the actors used to prove that two-dimensional sections remain chief.

Source: Aschbacher–Smith 14.7.22(2), using the parabolic in H.6.5.
-/

@[expose] public section
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

/-- The actual actor, as a subgroup of the original matrix group. -/
def actor : Subgroup Group :=
  (pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
    Matrix.PSL3Two.lineParabolicSL.subtype

theorem actor_eq_lineA : actor = Matrix.PSL3Two.MarkedAutomorphisms.lineA :=
  Matrix.PSL3Two.MarkedAutomorphisms.line_residual

section Transport
variable {G H M N : Type*} [_root_.Group G] [_root_.Group H]
  [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]
  {ρ : Representation (ZMod 2) G M} {σ : Representation (ZMod 2) G N}

/-- Restrict the same intertwining linear equivalence along the literal actor map. -/
noncomputable def restrictEquiv (e : ρ.Equiv σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  .mk e.toLinearEquiv (fun h => e.toIntertwiningMap.isIntertwining' (f h))

end Transport

/-- Every residual actor lies in the original marked line parabolic. -/
theorem actor_le_lineParabolic : actor ≤ Matrix.PSL3Two.lineParabolicSL := by
  rintro g ⟨x, _, rfl⟩
  exact x.property

/-- Cubic elements of the parabolic survive in its literal two-residual. -/
theorem mem_actor_of_cube (g : Group) (hg : g ∈ Matrix.PSL3Two.lineParabolicSL)
    (h3 : g ^ 3 = 1) : g ∈ actor := by
  let x : Matrix.PSL3Two.lineParabolicSL := ⟨g, hg⟩
  have hx3 : x ^ 3 = 1 := Subtype.ext h3
  exact ⟨x, Subgroup.mem_pResidual_of_orderOf_coprime
    (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hx3) (by decide)), rfl⟩

/-- The concrete cubic used by the cyclic-seed argument belongs to the actor. -/
theorem lineCycle_mem_actor : lineCycle ∈ actor :=
  mem_actor_of_cube lineCycle lineCycle_mem lineCycle_cube

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
