module
public import Theory.Representation.BinaryPermutationNaturalStructure
/-!
# Proper invariant subspaces of the binary natural module and its cover

The natural alternating module is irreducible. Every proper invariant
subspace of the augmentation core is constant, hence fixed by the full
symmetric group. In particular the central constant line in even degree
is retained. These facts detect movement in central extensions without
identifying a seed centralizer with the centralizer on the entire module.

Source: Aschbacher--Smith, B.3.1, printed p.83; application to the final
point-parabolic argument of 13.8.1, printed pp.968--969.
-/
public section
namespace BinaryPermutation
open Representation
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem natural_invariant_eq_bot_of_ne_top
    (hn : 5 ≤ Fintype.card Ω) (W : Submodule (ZMod 2) (natural Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, naturalRepresentation Ω g.val v ∈ W)
    (hproper : W ≠ ⊤) : W = ⊥ := by
  let : IsIrreducible (alternatingNaturalRepresentation Ω) := alternatingNatural_isIrreducible hn
  let S : Subrepresentation (alternatingNaturalRepresentation Ω) := ⟨W, fun g _ hv => hW g _ hv⟩
  rcases eq_bot_or_eq_top S with h | h
  · exact congrArg Subrepresentation.toSubmodule h
  · exact (hproper (congrArg Subrepresentation.toSubmodule h)).elim

theorem core_proper_invariant_fixed
    (hn : 5 ≤ Fintype.card Ω) (W : Submodule (ZMod 2) (core Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, coreRepresentation Ω g.val v ∈ W)
    (hproper : W ≠ ⊤) :
    ∀ g : Equiv.Perm Ω, ∀ v ∈ W, coreRepresentation Ω g v = v := by
  let D := W.map (core Ω).subtype
  have hD : ∀ g : alternatingGroup Ω, ∀ v ∈ D, representation Ω g.val v ∈ D := by
    rintro g _ ⟨v,hv,rfl⟩
    exact ⟨coreRepresentation Ω g.val v,hW g v hv,rfl⟩
  rcases invariant_le_constants_or_core_le hn D hD with hc | hc
  · intro g v hv
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hc ⟨v,hv,rfl⟩)
    apply Subtype.ext
    change representation Ω g v.val = v.val
    change c • allOne Ω = v.val at hc
    rw [← hc, map_smul, permute_allOne]
  · apply (hproper ?_).elim
    apply top_unique
    intro v _
    obtain ⟨w,hw,he⟩ := hc v.property
    exact (Subtype.ext he : w = v) ▸ hw
end BinaryPermutation
