module

public import Theory.Representation.BinaryConjugationSection.Generation

/-!
# Comparing quotient actions and moving homogeneous copies

A surjective coordinate map determines its conjugation action uniquely.
An additive homogeneous realization then transfers single-copy displacement
bounds to the full binary coinvariant kernel, by inserting one coordinate
at a time and summing. The multiplicity may be zero, and no scalar structure
on the single-copy additive group is required.

These are the action-comparison and additive-span steps used for the literal
quotients in Aschbacher--Smith, 11.5.7, printed p.781.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {ρ τ : Representation (ZMod 2) H M}

/-- Identical surjective section coordinates determine identical actor actions. -/
theorem action_eq_of_coordinates_eq (s : BinaryConjugationSection H A B ρ)
    (t : BinaryConjugationSection H A B τ) (he : s.coordinates = t.coordinates) :
    ρ = τ := by
  ext h v
  obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd v)
  have hs := s.equivariant h a
  have ht := t.equivariant h a
  rw [← he] at ht
  rw [ha] at hs ht
  exact hs.symm.trans ht

end Representation.BinaryConjugationSection

namespace Representation
variable {H : Type*} [Group H] {M W : Type*} [AddCommGroup M] [AddCommGroup W]
  [Module (ZMod 2) M]
  (ρ : Representation (ZMod 2) H M) {r : ℕ}
  (e : M ≃+ (Fin r → W)) (γ : H → W →+ W)
  (he : ∀ h v i, e (ρ h v) i = γ h (e v i))

include he in
/-- Single-copy additive displacement bounds hold independently in every coordinate. -/
theorem copies_mem_coinvariants (A : AddSubgroup W)
    (hA : ∀ C : AddSubgroup W, (∀ h w, γ h w - w ∈ C) → A ≤ C)
    (v : Fin r → W) (hv : ∀ i, v i ∈ A) : e.symm v ∈ Coinvariants.ker ρ := by
  classical
  have hsingle (i : Fin r) (w : W) (hw : w ∈ A) :
      e.symm (Pi.single i w) ∈ Coinvariants.ker ρ := by
    let f : W →+ M := e.symm.toAddMonoidHom.comp
      (AddMonoidHom.single (fun _ : Fin r => W) i)
    apply (hA ((Coinvariants.ker ρ).toAddSubgroup.comap f) ?_) hw
    intro h z
    change e.symm (Pi.single i (γ h z - z)) ∈ Coinvariants.ker ρ
    have haction : ρ h (e.symm (Pi.single i z)) =
        e.symm (Pi.single i (γ h z)) := by
      apply e.injective
      ext j
      rw [he, e.apply_symm_apply, e.apply_symm_apply]
      by_cases hij : i = j
      · subst j; simp
      · simp [Pi.single_eq_of_ne (Ne.symm hij)]
    have h := Coinvariants.sub_mem_ker (ρ := ρ) h (e.symm (Pi.single i z))
    rw [haction, ← map_sub, ← Pi.single_sub] at h
    exact h
  have hsum : ∑ i : Fin r, Pi.single i (v i) = v := by ext; simp
  have hm := (Coinvariants.ker ρ).sum_mem
    (t := Finset.univ) (fun i _ => hsingle i (v i) (hv i))
  simpa only [← map_sum, hsum] using hm

end Representation

