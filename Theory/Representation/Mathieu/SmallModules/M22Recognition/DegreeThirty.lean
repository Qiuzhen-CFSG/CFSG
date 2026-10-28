module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.Restriction
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule

/-!
# The binary M22 degree gap through thirty

Every faithful irreducible binary representation of the actual M22 of degree
at most thirty has degree ten. A simple submodule of its native point restriction
has degree one, nine or sixteen. The fixed-line argument handles degree one;
the checked Hermitian and adjoint inductions handle degrees nine and sixteen.
This uses neither semisimplicity of the restriction nor absolute irreducibility
of the binary module. The earlier conditional assembly remains available.

Source: Guralnick–Malle I, Proposition 5.1, pp.15–16, and Theorem 6.6/Table 6.7;
Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
-/

public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty

/-- The precise two point-submodule branches suffice for the M22 degree gap.
The branch premises must be discharged in the unconditional assembly. -/
theorem finrank_eq_ten_of_point_submodule_cases
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30)
    (hnine : ∀ S : Subrepresentation (pointRestriction σ),
      S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 9 →
        Module.finrank (ZMod 2) V = 10)
    (hsixteen : ∀ S : Subrepresentation (pointRestriction σ),
      S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 16 → False) :
    Module.finrank (ZMod 2) V = 10 := by
  rcases finrank_eq_ten_or_point_submodule σ hf hd with h | ⟨S, hS, h9 | h16⟩
  · exact h
  · exact hnine S hS h9
  · exact (hsixteen S hS h16).elim

/-- Every faithful irreducible binary M22 module of degree at most thirty has
degree ten, with both nontrivial point-submodule branches discharged. -/
theorem finrank_eq_ten_of_le_thirty
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30) :
    Module.finrank (ZMod 2) V = 10 := by
  apply finrank_eq_ten_of_point_submodule_cases σ hf hd
  · intro S hS h9
    let : S.toRepresentation.IsIrreducible := hS
    exact NineSubmodule.finrank_eq_ten σ hf hd S h9
  · exact SixteenSubmodule.impossible σ hf hd

/-- The degree-twelve bound needed by component recognition follows throughout
the binary degree-thirty window. -/
theorem finrank_le_twelve_of_le_thirty
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  rw [finrank_eq_ten_of_le_thirty σ hf hd]
  decide

end Representation.MathieuSmall.M22Recognition.DegreeThirty
