module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.Reduction
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The faithful representation of a full symplectic preimage

Restrict the actual matrix action on the four-dimensional ternary vector
space to the full inverse image of a projective subgroup. It remains faithful.
Its irreducibility is exactly the absence of the invariant subspaces used in
the projective subgroup interface: both quantify over every symplectic lift,
including the scalar kernel.

This interface permits applying representation theory without replacing the
matrix carrier or confusing a projective action with an action on vectors.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three

/-- The actual four-dimensional ternary action of the full inverse image. -/
@[expose] public noncomputable def fullPreimageRepresentation
    (M : Subgroup (PSp 2 (ZMod 3))) :
    Representation (ZMod 3) (fullPreimage M) (Vector 2 (ZMod 3)) :=
  Representation.ofDistribMulAction (ZMod 3) (fullPreimage M) (Vector 2 (ZMod 3))

/-- Restricting the symplectic matrix action preserves faithfulness. -/
public theorem fullPreimageRepresentation_injective (M : Subgroup (PSp 2 (ZMod 3))) :
    Function.Injective (fullPreimageRepresentation M) := by
  intro x y h
  apply Subtype.ext
  refine FaithfulSMul.eq_of_smul_eq_smul (fun v : Vector 2 (ZMod 3) => ?_)
  exact congrArg (fun f : Module.End (ZMod 3) (Vector 2 (ZMod 3)) => f v) h

/-- The two irreducibility conventions agree on the same full inverse image. -/
public theorem fullPreimageRepresentation_irreducible_iff
    (M : Subgroup (PSp 2 (ZMod 3))) :
    Representation.IsIrreducible (fullPreimageRepresentation M) ↔
      ¬ HasInvariantSubspace M := by
  constructor
  · intro h ⟨W, h0, h1, hW⟩
    let I : Subrepresentation (fullPreimageRepresentation M) := {
      toSubmodule := W
      apply_mem_toSubmodule := fun g v hv => hW g.val g.prop v hv }
    rcases IsSimpleOrder.eq_bot_or_eq_top I with hb | ht
    · exact h0 (congrArg Subrepresentation.toSubmodule hb)
    · exact h1 (congrArg Subrepresentation.toSubmodule ht)
  · intro h
    have hne : (⊥ : Subrepresentation (fullPreimageRepresentation M)) ≠ ⊤ := by
      intro heq
      have heq' : (⊥ : Submodule (ZMod 3) (Vector 2 (ZMod 3))) = ⊤ :=
        congrArg Subrepresentation.toSubmodule heq
      exact bot_ne_top heq'
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
    intro W
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    by_cases h1 : W = ⊤
    · exact Or.inr h1
    apply False.elim
    apply h
    refine ⟨W.toSubmodule, ?_, ?_, ?_⟩
    · exact fun heq => h0 (Subrepresentation.toSubmodule_injective heq)
    · exact fun heq => h1 (Subrepresentation.toSubmodule_injective heq)
    · intro g hg v hv
      exact W.apply_mem_toSubmodule (⟨g, hg⟩ : fullPreimage M) hv

end Matrix.PSp4Three
