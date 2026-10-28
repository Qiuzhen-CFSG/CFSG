module

public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightSylow

/-!
# Intrinsic permutation-module geometry for Section 12.6

The seven-dimensional augmentation core and its six-dimensional natural
quotient are kept separate. A core subspace whose nonzero words all have
weight four projects injectively to a totally singular subspace of the
natural quotient. Nondegeneracy of the polar form bounds its dimension by
three. The two source alternatives therefore give intersection corank at
least four and three, respectively.

The Sylow-fixed stabilizer calculation is transported along the actual
actor and module markings, separately for A₈ and S₈. In particular an A₈
Sylow subgroup is never treated as an S₈ Sylow subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §12.6, printed pp.822–838 (PDF pp.839–855),
especially 12.6.1 and the dimension inference in 12.6.20(3). These are
intrinsic calculations; the conjugate-intersection weight hypothesis is
supplied by the source centralizer and fusion argument. The remaining
orbit, marked-subspace and elementary-actor calculations are separate
obligations before the entire Section 12.6 permutation task is complete.
-/

public section
open Module BinaryPermutation
open BinaryPermutation.TerminalOrthogonal.Eight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

namespace CFSG.Quasithin.Chapter12.Section06.Permutation

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The core case of the dimension inference in 12.6.20(3). The input is
the actual weight-four conclusion on the nonzero intersection vectors. -/
theorem core_intersection_bound (e : V ≃ₗ[ZMod 2] core (Fin 8))
    (A B : Submodule (ZMod 2) V)
    (h : ∀ v ∈ A ⊓ B, v ≠ 0 → hammingNorm (e v).val = 4) :
    finrank (ZMod 2) (A ⊓ B : Submodule (ZMod 2) V) ≤ 3 ∧
      4 ≤ finrank (ZMod 2) (V ⧸ (A ⊓ B)) := by
  have hb := EightGeometry.finrank_weight_four_le ((A ⊓ B).map e.toLinearMap) (by
    rintro _ ⟨v, hv, rfl⟩ hn
    exact h v hv (fun hz => hn (by simp [hz])))
  rw [e.finrank_map_eq] at hb
  have hd : finrank (ZMod 2) V = 7 :=
    e.finrank_eq.trans (by simpa using finrank_core (Fin 8))
  have hc := (A ⊓ B).finrank_quotient_add_finrank
  exact ⟨hb, by omega⟩

/-- The natural-quotient case of the dimension inference in 12.6.20(3).
Singularity is measured using the genuine half-weight quadratic form. -/
theorem natural_intersection_bound (e : V ≃ₗ[ZMod 2] natural (Fin 8))
    (A B : Submodule (ZMod 2) V)
    (h : ∀ v ∈ A ⊓ B, v ≠ 0 → form (e v) = 0) :
    finrank (ZMod 2) (A ⊓ B : Submodule (ZMod 2) V) ≤ 3 ∧
      3 ≤ finrank (ZMod 2) (V ⧸ (A ⊓ B)) := by
  have hb := EightGeometry.finrank_nonzero_singular_le ((A ⊓ B).map e.toLinearMap) (by
    rintro _ ⟨v, hv, rfl⟩ hn
    exact h v hv (fun hz => hn (by simp [hz])))
  rw [e.finrank_map_eq] at hb
  have hd : finrank (ZMod 2) V = 6 := e.finrank_eq.trans finrank_natural
  have hc := (A ⊓ B).finrank_quotient_add_finrank
  exact ⟨hb, by omega⟩

variable {H : Type*} [Group H]

omit [FiniteDimensional (ZMod 2) V] in
/-- In the S₈ source marking, the stabilizer of a nonzero Sylow-fixed
vector is the pullback of a conjugate of the unordered four-block stabilizer. -/
theorem marked_symmetric_sylow_stabilizer (ρ : Representation (ZMod 2) H V)
    (a : H ≃* Equiv.Perm (Fin 8)) (e : V ≃ₗ[ZMod 2] natural (Fin 8))
    (he : ∀ g v, e (ρ g v) = naturalRepresentation (Fin 8) (a g) (e v))
    (P : Sylow 2 (Equiv.Perm (Fin 8))) (v : V) (hv : v ≠ 0)
    (hfixed : ∀ g : H, a g ∈ (P : Subgroup (Equiv.Perm (Fin 8))) → ρ g v = v) :
    ∃ r : Equiv.Perm (Fin 8), ∀ g : H,
      ρ g v = v ↔ r * a g * r⁻¹ ∈ fourStabilizer := by
  have hn : e v ≠ 0 := fun h => hv (e.injective (h.trans e.map_zero.symm))
  have hf : ∀ g ∈ (P : Subgroup (Equiv.Perm (Fin 8))),
      naturalRepresentation (Fin 8) g (e v) = e v := by
    intro g hg
    simpa only [he, a.apply_symm_apply] using
      congrArg e (hfixed (a.symm g) (by simpa using hg))
  obtain ⟨r, hr⟩ := EightSylowFixed.exists_conjugate_stabilizer P (e v) hn hf
  refine ⟨r, fun g => ?_⟩
  rw [← hr (a g), ← he]
  exact e.injective.eq_iff.symm

omit [FiniteDimensional (ZMod 2) V] in
/-- The A₈ source marking uses conjugacy inside A₈ and the actual alternating
Sylow subgroup. The conclusion retains the original action and vector. -/
theorem marked_alternating_sylow_stabilizer (ρ : Representation (ZMod 2) H V)
    (a : H ≃* alternatingGroup (Fin 8)) (e : V ≃ₗ[ZMod 2] natural (Fin 8))
    (he : ∀ g v, e (ρ g v) = naturalRepresentation (Fin 8) (a g).val (e v))
    (P : Sylow 2 (alternatingGroup (Fin 8))) (v : V) (hv : v ≠ 0)
    (hfixed : ∀ g : H, a g ∈ (P : Subgroup (alternatingGroup (Fin 8))) → ρ g v = v) :
    ∃ r : alternatingGroup (Fin 8), ∀ g : H,
      ρ g v = v ↔ r.val * (a g).val * r.val⁻¹ ∈ fourStabilizer := by
  have hn : e v ≠ 0 := fun h => hv (e.injective (h.trans e.map_zero.symm))
  have hf : ∀ g ∈ (P : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val (e v) = e v := by
    intro g hg
    simpa only [he, a.apply_symm_apply] using
      congrArg e (hfixed (a.symm g) (by simpa using hg))
  obtain ⟨r, hr⟩ := alternating_exists_conjugate_stabilizer P (e v) hn hf
  refine ⟨r, fun g => ?_⟩
  rw [← hr (a g).val, ← he]
  exact e.injective.eq_iff.symm

end CFSG.Quasithin.Chapter12.Section06.Permutation
