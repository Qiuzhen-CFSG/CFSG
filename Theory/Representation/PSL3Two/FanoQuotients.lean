module

public import Theory.Representation.PSL3Two.FanoCoreStructure

/-!
# Discarding the unwanted factors of the binary flag module

The trivial factor and the line core have respectively the trivial and
natural-dual simple heads. If a quotient of the flag permutation module
has neither of these simple quotients, it is already a quotient of the
point core plus the adjoint module. The proof applies the valid
simple-head quotient-surjectivity lemma twice; it makes no claim that
the discarded factors lie in the original kernel.

This is the quotient reduction in Aschbacher–Smith H.6.5, printed p.388
of the combined manuscript of 1 March 2004, using the correction to H.6.4.
The source's cyclic-generator hypotheses must separately exclude the two
unwanted quotients; those exclusions are explicit in this module.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Representation
namespace BinaryLinearThree.FanoQuotients
open FanoDecomposition FanoCoreStructure

abbrev trivialRepresentation : Representation (ZMod 2) Group (ZMod 2) :=
  Representation.trivial (ZMod 2) Group (ZMod 2)

abbrev Rest := Core × (LineCore × Steinberg)
noncomputable def restRepresentation : Representation (ZMod 2) Group Rest :=
  U₂.prod (lineCoreRepresentation.prod S)

/-- The trivial factor in the decomposed flag module. -/
noncomputable def trivialInclusion : trivialRepresentation.IntertwiningMap targetRepresentation :=
  IntertwiningMap.inl (ZMod 2) trivialRepresentation restRepresentation

/-- Inclusion of the three nontrivial factors in the decomposed flag module. -/
noncomputable def restInclusion : restRepresentation.IntertwiningMap targetRepresentation :=
  IntertwiningMap.inr (ZMod 2) trivialRepresentation restRepresentation

/-- The line-core factor in the three-factor remainder. -/
noncomputable def lineInclusion : lineCoreRepresentation.IntertwiningMap restRepresentation :=
  (IntertwiningMap.inr (ZMod 2) U₂ (lineCoreRepresentation.prod S)).comp
    (IntertwiningMap.inl (ZMod 2) lineCoreRepresentation S)

/-- The two retained factors, embedded around the line-core factor. -/
noncomputable def retainedInclusion : (U₂.prod S).IntertwiningMap restRepresentation :=
  (IntertwiningMap.inl (ZMod 2) U₂ (lineCoreRepresentation.prod S)).comp
      (IntertwiningMap.fst (ZMod 2) U₂ S) +
    ((IntertwiningMap.inr (ZMod 2) U₂ (lineCoreRepresentation.prod S)).comp
      (IntertwiningMap.inr (ZMod 2) lineCoreRepresentation S)).comp
      (IntertwiningMap.snd (ZMod 2) U₂ S)

@[simp] theorem lineInclusion_apply (l : LineCore) : lineInclusion l = (0, (l, 0)) := rfl

@[simp] theorem retainedInclusion_apply (a : Core × Steinberg) :
    retainedInclusion a = (a.1, (0, a.2)) := by
  change ((a.1, (0, 0)) : Rest) + (0, (0, a.2)) = _
  simp

universe u
variable {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

/-- First discard the trivial factor, using its actual unique simple quotient. -/
theorem rest_surjective (ρ : Representation (ZMod 2) Group M)
    (q : targetRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hno : ∀ f : ρ.IntertwiningMap trivialRepresentation, ¬ Function.Surjective f) :
    Function.Surjective (q.comp restInclusion) := by
  refine SimpleHeadQuotient.surjective_right_of_unique_irreducible_quotient
    (A := ZMod 2) (B := Rest) (S := ZMod 2) (M := M)
    (α := trivialRepresentation) (β := restRepresentation) (ρ := ρ)
    (σ := trivialRepresentation) (q.comp trivialInclusion) (q.comp restInclusion) ?_ ?_ hno
  · apply Submodule.eq_top_iff'.mpr
    intro m
    obtain ⟨⟨c, a⟩, rfl⟩ := hq m
    refine Submodule.mem_sup.mpr
      ⟨q (c, 0), ⟨c, rfl⟩, q (0, a), ⟨a, rfl⟩, ?_⟩
    rw [← map_add]
    simp
  · intro T _ _ τ hτ f hf
    let : IsIrreducible τ := hτ
    let : Nontrivial T := Subrepresentation.irreducible_module_nontrivial τ
    apply IrreducibleCatalogue.simple_quotient_of_binary_trivial f
    intro hz
    obtain ⟨t, ht⟩ := exists_ne (0 : T)
    obtain ⟨a, ha⟩ := hf t
    exact ht (ha.symm.trans (by simp [hz]))

/-- Then discard the line core by its proved dual-natural simple head. -/
theorem retained_surjective (ρ : Representation (ZMod 2) Group M)
    (q : restRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hno : ∀ f : ρ.IntertwiningMap W.dual, ¬ Function.Surjective f) :
    Function.Surjective (q.comp retainedInclusion) := by
  refine SimpleHeadQuotient.surjective_right_of_unique_irreducible_quotient
    (A := LineCore) (B := Core × Steinberg) (S := Dual) (M := M)
    (α := lineCoreRepresentation) (β := U₂.prod S) (ρ := ρ) (σ := W.dual)
    (q.comp lineInclusion) (q.comp retainedInclusion) ?_ ?_ hno
  · apply Submodule.eq_top_iff'.mpr
    intro m
    obtain ⟨⟨a, l, s⟩, rfl⟩ := hq m
    refine Submodule.mem_sup.mpr
      ⟨q (0, (l, 0)), ⟨l, rfl⟩, q (a, (0, s)), ⟨(a, s), ?_⟩, ?_⟩
    · change q (retainedInclusion (a, s)) = _
      rw [retainedInclusion_apply]
    · rw [← map_add]
      simp
  · intro T _ _ τ hτ f hf
    let : IsIrreducible τ := hτ
    exact lineCore_simple_quotient τ f hf

/-- Correct H.6.5 quotient reduction on the literal four-factor carrier. -/
theorem quotient_of_target (ρ : Representation (ZMod 2) Group M)
    (q : targetRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (htriv : ∀ f : ρ.IntertwiningMap trivialRepresentation, ¬ Function.Surjective f)
    (hdual : ∀ f : ρ.IntertwiningMap W.dual, ¬ Function.Surjective f) :
    ∃ f : (U₂.prod S).IntertwiningMap ρ, Function.Surjective f := by
  exact ⟨(q.comp restInclusion).comp retainedInclusion,
    retained_surjective ρ _ (rest_surjective ρ q hq htriv) hdual⟩

/-- Correct H.6.5 quotient reduction for the actual twenty-one flags. -/
theorem quotient_of_flags (ρ : Representation (ZMod 2) Group M)
    (q : flagRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (htriv : ∀ f : ρ.IntertwiningMap trivialRepresentation, ¬ Function.Surjective f)
    (hdual : ∀ f : ρ.IntertwiningMap W.dual, ¬ Function.Surjective f) :
    ∃ f : (U₂.prod S).IntertwiningMap ρ, Function.Surjective f :=
  quotient_of_target ρ (q.comp flagDecomposition.symm.toIntertwiningMap)
    (hq.comp flagDecomposition.symm.toLinearEquiv.surjective) htriv hdual

end BinaryLinearThree.FanoQuotients
