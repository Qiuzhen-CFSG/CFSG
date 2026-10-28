module

public import CFSG.Quasithin.ChapterG.Section05.Basic
public import Theory.Representation.BinaryAlternatingSixModels.Geometry

/-!
# Concrete simple-module models for G.5.1 and the line exclusion in G.5.2

The first natural action is the published duad action from `Section05.Basic`.
The second is its twist by an explicit exceptional automorphism which exchanges
exactly the marked duad and syntheme parabolics. Both actions are irreducible;
the first parabolic fixes a point and no projective line on the first action,
and the second has the reversed behavior. This also proves inequivalence.

The tensor carrier and action are concrete. Exhaustion of the symmetric and
alternating simple modules, identification of the tensor with the Steinberg
module, and its irreducibility and splitting after extending scalars to F₄ are
still separate obligations. The recognition theorem below is deliberately
conditional on the four-model alternative. It excludes three alternatives by
the proved geometry and retains an actual equivariant isomorphism to the tensor.
It is not an unconditional assertion of G.5.1 or G.5.2.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–2,
printed pp.342–343 (PDF pp.353–354).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section05
open Theory.SpecificGroups.SymmetricSix BinaryAlternatingSix Representation

/-- The published first natural action has the source point/line marking. -/
theorem first_natural_parabolic_geometry :
    (∃ v : NaturalModule, v ≠ 0 ∧ ∀ g ∈ G1, naturalAction g v = v) ∧
      HasInvariantLine naturalAction G2 ∧ ¬ HasInvariantLine naturalAction G1 :=
  ⟨⟨(polarVector 0).val, (polarVector 0).property, first_fixes_point⟩,
    first_has_line, first_has_no_line⟩

/-- The genuine exceptional twist reverses the two marked parabolics. -/
theorem second_natural_parabolic_geometry :
    (∃ v : NaturalModule, v ≠ 0 ∧ ∀ g ∈ G2, secondAlternating g v = v) ∧
      HasInvariantLine secondAlternating G1 ∧ ¬ HasInvariantLine secondAlternating G2 :=
  ⟨⟨(polarVector 0).val, (polarVector 0).property, second_fixes_point⟩,
    second_has_line, second_has_no_line⟩

/-- These are two inequivalent irreducible actions on the four-dimensional
natural carrier, not two names for one marked representation. -/
theorem natural_models_distinct :
    Module.finrank (ZMod 2) NaturalModule = 4 ∧
      IsIrreducible naturalAction ∧ IsIrreducible secondAlternating ∧
      IsEmpty (Representation.Equiv naturalAction secondAlternating) :=
  ⟨naturalModule_finrank, firstAlternating_irreducible,
    secondAlternating_irreducible, natural_inequivalent⟩

/-- The G.9 natural comparison retains the actual automorphism of A₆. The
existing G.9 coordinate equivalence then compares the duad and deleted models. -/
theorem natural_comparison_of_models {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (h : Nonempty (ρ.Equiv naturalAction) ∨ Nonempty (ρ.Equiv secondAlternating)) :
    ∃ α : MulAut G, ∃ e : V ≃ₗ[ZMod 2] NaturalModule,
      ∀ g v, e (ρ g v) = naturalAction (α g) (e v) :=
  natural_comparison ρ h

/-- The numerical consequence consumed by the small-degree branches of G.9
and K.1, conditional on the actual equivariant model alternative. -/
theorem alternating_degrees_of_models {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : IsAlternatingModel ρ) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 4 ∨
      Module.finrank (ZMod 2) V = 16 := by
  rcases h with h | h | h | h
  all_goals obtain ⟨e⟩ := h
  · exact Or.inl (e.toLinearEquiv.finrank_eq.trans (by simp))
  · exact Or.inr (Or.inl (e.toLinearEquiv.finrank_eq.trans naturalModule_finrank))
  · exact Or.inr (Or.inl (e.toLinearEquiv.finrank_eq.trans naturalModule_finrank))
  · exact Or.inr (Or.inr (e.toLinearEquiv.finrank_eq.trans tensor_finrank))

/-- The exclusion argument of G.5.2 on the literal source groups. The
symmetric catalogue and identification of `tensorAction` with Steinberg must
still be discharged before this yields the unconditional source theorem. -/
theorem tensor_recognition_of_models {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G0 V) (hmodel : IsSymmetricModel ρ)
    (h₁ : HasInvariantLine (ρ.comp G.subtype) G1)
    (h₂ : HasInvariantLine (ρ.comp G.subtype) G2) :
    Nonempty (ρ.Equiv tensorAction) :=
  tensor_of_invariant_lines_of_model ρ hmodel h₁ h₂

end CFSG.Quasithin.ChapterG.Section05
