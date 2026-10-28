module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Parity
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Nonsplitting
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.TwistedCohomology.Representatives

/-!
# The two factor-set classes for the twisted binary action of S4

Every normalized factor set for the published twisted action is equivalent to
the trivial factor set or the diagonal parity factor set. Changing the section
along generator words first kills the spanning-tree edges. Kernel-checked
polynomial elimination expresses the remaining values in five binary entries.
The thirty-two assignments have explicit cochain corrections on generators;
the cocycle identity extends these corrections to all pairs of permutations.

Together with `twistedFactorSet_not_equivalent_trivial`, this proves that there
are exactly two classes. It supplies the twisted-action cohomology input to the
independent finite extension argument for Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), p.314. No ambient-group, splitting, or classification hypothesis is
used here; the recognition theorem is assembled separately.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
open LocalModelDichotomy AbelianExtension
namespace TwistedCohomology

private theorem factorSet_ext (c d : FactorSet twistedAction)
    (h : ∀ s t, c.toFun s t = d.toFun s t) : c = d := by
  have hf : c.toFun = d.toFun := funext (fun s => funext (h s))
  cases c
  cases d
  cases hf
  rfl

private theorem eq_of_generator_values (c d : FactorSet twistedAction)
    (h : ∀ a t, c.toFun (perm (gen a)) (perm t) = d.toFun (perm (gen a)) (perm t)) :
    c = d := by
  apply factorSet_ext
  intro s t
  obtain ⟨s, rfl⟩ := perm_surjective s
  obtain ⟨t, rfl⟩ := perm_surjective t
  have he : (fun a t => c.toFun (perm (gen a)) (perm t)) =
      (fun a t => d.toFun (perm (gen a)) (perm t)) := funext (fun a => funext (h a))
  calc
    c.toFun (perm s) (perm t) =
        expand (fun a t => c.toFun (perm (gen a)) (perm t)) (words s) t := by
      rw [expand_eq, words_cover]
    _ = expand (fun a t => d.toFun (perm (gen a)) (perm t)) (words s) t := congrArg
      (fun e => expand e (words s) t) he
    _ = d.toFun (perm s) (perm t) := by rw [expand_eq, words_cover]

private theorem equivalent_of_generator_correction (c d : FactorSet twistedAction)
    (b : SymmetricFour → BinaryFour) (hb : b 1 = 1)
    (h : ∀ a t, c.toFun (perm (gen a)) (perm t) * b (perm (gen a) * perm t) =
      b (perm (gen a)) * twistedAction (perm (gen a)) (b (perm t)) *
        d.toFun (perm (gen a)) (perm t)) : c.Equivalent d := by
  have he : c = changeBy d b hb := by
    apply eq_of_generator_values
    intro a t
    change c.toFun (perm (gen a)) (perm t) =
      b (perm (gen a)) * twistedAction (perm (gen a)) (b (perm t)) *
        d.toFun (perm (gen a)) (perm t) * (b (perm (gen a) * perm t))⁻¹
    rw [← h]
    exact (mul_inv_cancel_right _ _).symm
  rw [he]
  exact (equivalent_changeBy d b hb).symm

private noncomputable def cochain (k : Fin 32) (s : SymmetricFour) : BinaryFour :=
  cochainAt k (Classical.choose (perm_surjective s))

private theorem cochain_perm (k : Fin 32) (s : Fin 24) :
    cochain k (perm s) = cochainAt k s := by
  have h : Classical.choose (perm_surjective (perm s)) = s :=
    perm_injective (Classical.choose_spec (perm_surjective (perm s)))
  simp only [cochain, h]

private theorem normalized_classes (c : FactorSet twistedAction) (hc : Normalized c) :
    c.Equivalent (FactorSet.trivial twistedAction) ∨ c.Equivalent twistedFactorSet := by
  obtain ⟨k, hk⟩ := parameters_cover (fun j => coordinates c (freePositions j))
  have hx : coordinates c = family (parametersAt k) := by
    rw [hk]
    exact coordinates_from_five (coordinates c) (coordinates_cocycle c hc)
  have hequiv : c.Equivalent (representative k) := by
    apply equivalent_of_generator_correction c (representative k) (cochain k)
    · rw [← perm_zero, cochain_perm, cochainAt_zero]
    · intro a t
      rw [← perm_mul, cochain_perm, cochain_perm, cochain_perm,
        ← table_coordinates c hc, hx]
      exact correction_table k a t
  unfold representative at hequiv
  cases h : classAt k with
  | false => exact Or.inl (by simpa only [h, Bool.false_eq_true, ↓reduceIte] using hequiv)
  | true => exact Or.inr (by simpa only [h, ↓reduceIte] using hequiv)

end TwistedCohomology

/-- Every factor set for the twisted binary action of S4 is cohomologous to
one of the trivial and diagonal parity factor sets. -/
public theorem twistedFactorSet_classes (c : FactorSet twistedAction) :
    c.Equivalent (FactorSet.trivial twistedAction) ∨ c.Equivalent twistedFactorSet := by
  rcases TwistedCohomology.normalized_classes (TwistedCohomology.normalize c)
      (TwistedCohomology.normalized_normalize c) with h | h
  · exact Or.inl ((TwistedCohomology.equivalent_normalize c).trans h)
  · exact Or.inr ((TwistedCohomology.equivalent_normalize c).trans h)

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
